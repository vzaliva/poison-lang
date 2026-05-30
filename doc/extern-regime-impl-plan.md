# Extern-Regime Implementation Plan (executable, green-checkpointed)

Implements `doc/extern-regime.md`. Hard constraint: **no new `sorry`/axioms** at any
checkpoint. Baseline (this branch `poison-ffi-regime-ext`) is fully proven: 0 sorry, 0
custom axioms, `lake build LeanProofs.FaultRobustnessProofs` green (7775 jobs).

## Architectural findings (discriminator + crux already verified)

- **Threaded regime invariant is NOT domain-exact.** `regimeConsistentWithCtx ctx :=
  tagEnvConsistentWithRegime ctx.tagEnv ctx.regime`, i.e. `∀k, tagEnv[k]=true →
  regime[k]=true` (RegimeConsistency.lean:1260-1266). Inserting a fresh regime entry
  for a tag not (yet) true in `tagEnv` cannot break it. => tractable branch.
- **Domain-exactness (`wfRegime`, `consistentRegimeSpec`, the bridge
  `consistentRegimeSpec_implies_consistentWithRegime`) is INITIAL-STATE ONLY**
  (FaultRobustnessProofs.lean:3002-3012; StepFR.lean:156-164). The regime only grows
  *during* stepping; the initial regime is exactly `inputSpecTags`. => the bridge and
  initial machinery need **no change** (fresh extern tags are ≥ initial `nextTag`).
- **`ExternBoundarySpec` is a bundle of ASSUMED contracts** (`declFR/callFR/declSingle/
  callSingle/operational`) carried per `TrustedExternEntry`/`TrustedRegistry`
  (ExternBoundary.lean:316-443). => §4.4 two-run obligation is a NEW ASSUMED field,
  discharged at the trust boundary, consumed in StepFRApp — not a runtime proof.
- **No deriving on `TypeContext`/`TypeResult`** => a function-typed policy field is safe.
- **Construction is `{ctx with ...}`-dominant** => new field threads for free; only ~12
  from-scratch `TypeContext` literals + `initialTypeContext` (Main.lean:120) need the field.
- **Crux dischargeable**: the extern-result `valueConsistentWithRegime` is already built
  by-cases on `R.lookup? k` (StepFRApp.lean:2218-2242) and already supplies
  `closureCapturedVarsRegime`. Adding `R(k)=b` only needs `qtypPredHolds`/`¬qtypPredHolds`
  from the new contract to pick `inRegimeTrue`/`inRegimeFalse`.
- **Monotonicity cost is ~90 producer sites + ~15 transport lemmas**, not 268. The
  transport lemmas (`locsRegime_monotone`, `valueConsistentWithRegime` transfer, etc.)
  only need old-tag backward transport, which `monotoneStepExt` + `¬newTags k` supplies.
  `regime_monotone` (TypeSafety.lean:3809) ← `typecheck_regime_mono_main` is the master.
  `masked_lookup_none_of_monotoneStep` (25 sites): one new freshness lemma (masked tags
  are old / `< nextTag`; fresh extern tags are `≥ nextTag` — disjoint).

## Policy shape (resolves Q1, Q4)

- `InputSpec.regimeExterns : List ExternId` (data; Repr-safe).
- `TypeContext.externRegime : ExternId → Tag → Option Bool` (proof granularity; default
  `fun _ _ => none`). Threads via `{ctx with}`. `some b` ⇒ insert `k ↦ b` into `regime'`;
  `none` ⇒ leave `k` out (conservative path preserved).
- Executable CLI granularity `ExternId → Option Bool` is a restriction (every output tag
  of the id gets the same bool); wired in Main via `--extern-regime`.

## Regime-evolution relation (resolves Q2)

```
def Regime.monotoneStepExt (R R' : Regime) (newTags : Tag → Prop) : Prop :=
  (∀ k b, R.lookup? k = some b → (R'.lookup? k = some b ∨ R'.lookup? k = none)) ∧  -- unchanged
  (∀ k, R'.lookup? k ≠ none → R.lookup? k ≠ none ∨ newTags k)
-- monotoneStep R R' = monotoneStepExt R R' (fun _ => False)
-- newTags for a step = (fun k => ctx.nextTag ≤ k)  (freshly allocated this step)
-- backward transport for k with ¬newTags k: from conj2 R[k]≠none, conj1 gives value match.
```

## Phases (each ends GREEN, no new sorry/axiom)

- **Phase A — data plumbing (green, no behavior change). ✅ DONE (full build 10839 jobs,
  0 sorry/0 axiom).** Added `InputSpec.regimeExterns : List ExternId := []` and
  `TypeContext.externRegime : ExternId → Tag → Option Bool := fun _ _ => none` (both
  defaulted). Default lets `{ ctx with … }` thread it for free; ~25 *full* TypeContext
  literals (those listing all 8 old fields, opening `{ pc :=`/`set X : TypeContext := {`
  or positional `⟨…⟩`) needed `externRegime := ctx.externRegime` added explicitly to match
  the typechecker's threaded `ctx.externRegime` (fixed in TypeSafety×10, StepFR×13,
  ExternBoundaryProofs×2). Fully-fresh literals (regime:={}) use `fun _ _ => none`.
  `{ X with … }` record-updates were left untouched. Nothing reads the fields yet.
- **Phase C-prep — additive weak relation (green).** Define `monotoneStepExt` + lemmas
  (`monotoneStep → monotoneStepExt`, backward transport under `¬newTags k`,
  `monotoneStepExt`-versions of transport lemmas, masked freshness lemma). Add ONLY new
  decls; touch no existing proof. ✅ checkpoint.
- **Phase B+C+D — atomic flip (one red→green transition).**
  - B: extern typing rules query `ctx.externRegime` and insert fresh selected tags into
    `regime'` (applyFnTClosure extern, applyFnTClosure' extern, typecheckExternVal,
    effects). `nextTag` bookkeeping unchanged.
  - C: `typecheck_regime_mono_main`/`regime_monotone` now conclude `monotoneStepExt` with
    `newTags = (ctx.nextTag ≤ ·)`. Migrate ~90 producers + retarget transport sites to
    the `monotoneStepExt` versions with discharged `¬newTags k` (old tags `< nextTag`).
    Add `regime_monotone` old-tag corollary for unchanged consumers.
  - D: new `ExternBoundarySpec.regimeFR` field (two-run: `R(k)=true ⇒ both runs'
    extern value/written cell satisfy pred; R(k)=false ⇒ both fail`). Consume in
    StepFRApp extern case to produce `valueConsistentWithRegime`/`consistentWithRegime`
    for fresh tags. Provide trivially at `TrustedRegistry` construction (trust).
  - ✅ checkpoint: full FR theorem holds for non-trivial policy.
- **Phase E — CLI + spec/docs.** `--extern-regime` parse + apply in Main; Ott
  `poison-lang.ott` + `doc/poison-lang-description.tex`; an `open`-shaped example
  (§4.6) as acceptance target. ✅ checkpoint.

## Difficulty estimate (corrected — earlier draft over-stated this)

The flip is a **bounded, mechanical-with-care** change, NOT "days/infeasible":
- **Freshness discharge is a one-liner from an EXISTING invariant.** `TagBoundedCtx`
  (already threaded in `StepFRPost`) bounds context/closure tags `< nextTag`; with
  `newTags = fun k => nextTag ≤ k`, every `¬ newTags k` discharge is `Nat.not_le.2 (bound …)`.
  No new deep-bound predicate; reuse `closureEnvBoundedInCtx` / `CapturedEnvFullBounded`.
- **masked-bounded threading is ~10-20 sites, trivial discharge.** `masked ≡ fun _ => False`
  at the top level (FaultRobustnessProofs.lean:2203), threaded unchanged; the bound
  `∀ k, masked k → k < ctx.nextTag` is concentrated in the `*_maskedReg_*` single-run
  lemmas + their dispatcher (the extern/masked path), discharged as `fun k hk => absurd hk id`
  at instantiation and re-established per sub-context by nextTag monotonicity.
- **Incremental-green wiring removes budget risk**: keep `regime_monotone` (monotoneStep) AND
  `regime_monotoneExt` (added) valid simultaneously pre-insertion; retarget consumers file by
  file (per-operator files are import-independent ⇒ parallel sub-agents), each a green
  checkpoint; remove `regime_monotone` only after Phase B. So a stop is always green.

## Masked-freshness complication (key risk for the flip — Q5)

`masked_lookup_none_of_monotoneStep` (25 sites) and `monotoneStep_lookup_back` use the
"no new tags" conjunct (`.2`). Under `monotoneStepExt` they need `masked k → ¬ newTags k`.
With `newTags = (ctx.nextTag ≤ ·)` this is `masked k → k < ctx.nextTag`. The top-level FR
proof instantiates `masked := fun _ => False` (FaultRobustnessProofs.lean:2203), but the
**if/ite cases introduce non-trivial masking** internally (the unknown-`if` guard tag is
added to `masked`; FaultRobustnessProofs.lean:672/710/717/901/964). Those masked guard tags
are allocated by the if-rule *before* the branches are typechecked, so extern tags allocated
in the branches are strictly larger ⇒ `masked < branch-start nextTag`. So the discharge is
sound but requires threading a **`masked k → k < ctx.nextTag` bound** through the masked
contracts (`regimeConsistentWithCtxMasked` / `consistentWithRegimeMasked` /
`StepFR…Masked…` / `ExternDeclBoundarySingleMaskedContract`). This is the most invasive part
of the flip (masked appears ~1481×, but the bound rides existing `{ctx with}` threading and
is preserved because `nextTag` only grows).

IMPORTANT — transport lemmas mostly use only `.1` (forward preservation), which is
*identical* between `monotoneStep` and `monotoneStepExt`. So `locsRegime_monotone`,
`varsRegime_monotone`, `valueConsistentWithRegime_monotone`,
`closureCapturedVarsRegime_monotone`, `consistentWithRegimeMasked_monotone`, etc. migrate by
just changing the hypothesis type to `monotoneStepExt R R' newTags` (body unchanged). Only
the two `.2` lemmas above need the freshness side condition.

## Flip execution guide (detailed, for continuation)

### Done so far (all green, 0 sorry/0 axiom)
- Phase A (data plumbing) — see above.
- **Transport-layer CRUX SOLVED** (the hardest part): `regime_monotoneExt` (TypeSafety);
  public bound extractors `CapturedEnvFullBounded_guardTag_lt`,
  `CapturedEnvFullBounded_member_etypClosures`, `qtypGuardTag_lt_of_predTagBounded` (TypeSafety,
  from the private `CapturedEnvFullBounded.get`); deep transport
  `deepValueQTypProperty_capturedVarsRegime_monotoneExt` + `closureCapturedVarsRegime_monotoneExt`
  + `valueConsistentWithRegime_monotoneExt` + `cleanUnder_of_monotoneExt`
  + `capturedVarsRegimeProperty_monotoneExt` (StepFR). Freshness `¬newTags k = k<B` discharged
  from `etypClosuresFullBounded`/`qtypPredTagBounded`; `hnewB : ∀k, newTags k → B ≤ k`.
- **Remaining transport `_ext` (mechanical mirrors)**: the Masked variants
  (`capturedVarsRegimePropertyMasked_monotone`, `closureCapturedVarsRegimeMasked_monotone`,
  `valueConsistentWithRegimeMasked_monotone`, `consistentWithRegimeMasked_monotone`,
  `memberVarsRegimeEvidence_monotone`). Cleanest: extract a GENERIC
  `deepValueQTypProperty_mono_bounded {P P' B} (hPP : ∀ σcap ρcap, CapturedEnvFullBounded σcap B →
  P σcap ρcap → P' σcap ρcap) (hdeep) : etypClosuresFullBounded qt.etyp B → deepValueQTypProperty P' qt v`
  (generalize the working `deepValueQTypProperty_capturedVarsRegime_monotoneExt`), then both the
  plain and Masked closure transports are 3-liners over it.
- Relation foundation (additive):
  - `Regime.monotoneStepExt R R' newTags`, `Regime.monotoneStep_toExt`,
    `Regime.monotoneStepExt_lookup_back` (LeanPoison/Typecheck.lean, after `monotoneStep`).
  - `masked_lookup_none_of_monotoneStepExt` (RegimeConsistency.lean, after the `_of_monotoneStep`).
  - `locsRegime_monotoneExt`, `varsRegime_monotoneExt` (FaultRobustness.lean, after the originals).
    These are `.1`-only (caller supplies `R'[k]=some b`) ⇒ NO freshness hypothesis.

### Transport-layer crux: `closureCapturedVarsRegime_monotoneExt`
This is the genuinely hard lemma. A naive `deepValueQTypProperty_mono₂` (zip two deep
derivations) is UNSOUND: the captured `σcap` is existentially chosen via
`FnTClosure.regular _ _ σcap ∈ tcls`, so two derivations over the same `(qt,v)` may pick
different `σcap`, breaking the per-level `hPP σcap ρcap (P σcap) (Q σcap)` join. Correct
approach: derive the per-level freshness `∀ k_x ∈ σcap-tags, ¬ newTags k_x` from the EXISTING
deep type bound `etypClosuresFullBounded qt.etyp B` (B = ctx.nextTag; bounds every `tcls`
captured guard tag `< B`), so whichever `σcap` the derivation chose, its tags are `< B`.
Needs a `deepValueQTypProperty`-shaped traversal that, at each closure level, extracts the
`σcap`-bound from `etypClosuresFullBounded` via the `FnTClosure.regular … σcap ∈ tcls`
membership. Build this as `closureCapturedVarsRegime_monotoneExt (hbound : <deep type bound>)`,
then `valueConsistentWithRegime_monotoneExt` follows (its `notInRegime` case needs `¬newTags`
for qt's own guard tag, from the same bound; other cases just call the closure variant).

Concrete pieces verified for this sub-project:
- `qtypPredTagBounded qt B ∧ qtypGuardTag qt = some k → k < B` (case on `qt.pred`;
  `predTagBounded`/`qtypGuardTag` both read guardClosure/guardOnly `k`). TypeSafety:4126-4134, 537.
- `CapturedEnvFullBounded env B → capturedPredTagsBounded env B` exists (TypeSafety:6157) and
  `capturedEnvBoundedN`'s `n+1` case recurses member closures (TypeSafety:6028) ⇒ member's nested
  closures are `CapturedEnvFullBounded`/`etypClosuresFullBounded`.
- **API GAP**: `capturedPredTagsBounded` (5931) and `capturedEnvBoundedN` (6028) are `private` to
  TypeSafety. The `_ext` lemma lives downstream (StepFR, where `closureCapturedVarsRegime_monotone`
  is), so first add PUBLIC extraction lemmas in TypeSafety:
  (a) `CapturedEnvFullBounded env B → (name,qt) ∈ env → qtypGuardTag qt = some k → k < B`;
  (b) `CapturedEnvFullBounded env B → (name,qt) ∈ env → etypClosuresFullBounded qt.etyp B`
  (member's deep closures bounded). Then build the deep transport on top.
- `etypClosuresFullBounded`/`CapturedEnvFullBounded` are public `def`s (6043/6047). The deep-type
  bound for a result/captured value is available at call sites from `TagBoundedCtx`/
  `closureEnvBoundedInCtx` (already in `StepFRPost`).
NOTE the `_ext` variants are ADDITIVE (revertible) ⇒ safe to develop without risking the green tree.

### Remaining transport `_ext` variants to add (additive, then retarget)
All use `.2` (backward) ⇒ each needs a freshness hypothesis. The uniform pattern: the
structure's guard tag `k` is OLD (`< B` where `newTags = fun k => B ≤ k`), so add
`hfresh` and discharge from `TagBoundedCtx` at the call site. Call-site counts (retarget cost):
- `capturedVarsRegimeProperty_monotone` (1) — `.2` at the `hkR` derivation; hfresh: captured-var tag old.
- `closureCapturedVarsRegime_monotone` (26) — wraps the above via `deepValueQTypProperty_mono`.
- `valueConsistentWithRegime_monotone` (14) — `.2` only in the `notInRegime` case; hfresh: qt's tag old.
- `memberVarsRegimeEvidence_monotone` (×2; 6) ; `*Masked_monotone` (capturedVarsRegimePropertyMasked,
  closureCapturedVarsRegimeMasked 13, valueConsistentWithRegimeMasked 5, consistentWithRegimeMasked 1).
- `cleanUnder_of_monotone` (15) — BACKWARD (R'-clean → R-clean); central to extern de-poisoning;
  uses `monotoneStepExt_lookup_back` + hfresh.
- StepFRVlet local cleanUnder lemmas (~2); `JoinMemberTransport` lemma (1; `.1`-only).
Freshness hyp shape options: per-tag `(hfresh : ∀ k, qtypGuardTag qt = some k → ¬ newTags k)`, or
per-structure for the captured-var/context lemmas. Prefer threading `TagBoundedCtx` and a single
helper `tag_lt_nextTag_of_*` so each discharge is uniform.

### STATUS: transport `_ext` infrastructure COMPLETE & green (10839-job build, 0 sorry/0 axiom)
Everything below ("Consumer retargeting", Phase B, D, E) remains. It is ONE coordinated
red→green transition (flipping `typecheck_regime_mono_main` to `monotoneStepExt` + adding
insertion simultaneously breaks all `regime_monotone` consumers), so it cannot be split into
smaller green checkpoints — best done compiler-driven with parallel per-operator sub-agents,
in a session with budget for many full (~10-min) build/fix rounds. All building blocks
(transport `_ext` lemmas, bound extractors, `regime_monotoneExt`) are in place.

### Consumer retargeting (~90 producer + ~86 transport sites)
1. `regime_monotone` (TypeSafety.lean:3809): change conclusion to
   `Regime.monotoneStepExt ctx.regime (ctxAfter ctx res).regime (fun k => ctx.nextTag ≤ k)`.
   Until Phase B, prove via `(typecheck_regime_mono_main … ).monotoneStep_toExt _` (still monotoneStep).
   `joinTypeResults_regime_monotone` (TypeSafety.lean:2931): same treatment (6 call sites).
2. ~90 producer annotations `have h : Regime.monotoneStep A B := regime_monotone …`
   → `have h : Regime.monotoneStepExt A B _ := regime_monotone …` (underscore newTags inferred ⇒
   no re-touch when Phase B changes the newTags instance). Sites: StepFRApp 56, StepFRVlet 14,
   StepFR 8, StepFRAssign 3, StepFRIte 3, StepFROp 2, StepFRSeq 2, FaultRobustnessProofs 1.
3. Transport call sites: `foo_monotone h …` → `foo_monotoneExt h … hfresh`. `h` now `monotoneStepExt`
   passes directly; supply `hfresh` from `TagBoundedCtx`. Genuine-`monotoneStep` callers (rare) lift
   via `h.monotoneStep_toExt _`.
4. `masked_lookup_none_of_monotoneStep` (23 sites: StepFRApp 12, StepFR 7, +Assign/Op/Seq/Vlet/FRProofs)
   → `_of_monotoneStepExt`, supplying `hmasked_fresh : ∀ k, masked k → ¬ newTags k`.
   Discharge needs **`hmasked_bounded : ∀ k, masked k → k < ctx.nextTag`** threaded into the enclosing
   lemmas (`typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv_main` + the StepFRApp masked
   helpers + the masked boundary contracts). masked ≡ `fun _ => False` at top level
   (FaultRobustnessProofs.lean:2203) ⇒ trivial at instantiation; threaded unchanged through IH;
   preserved because nextTag only grows. Re-establish per sub-context via the nextTag-mono lemma.

### Phase B — NEWLY-SURFACED PREREQUISITE: regime-domain-bounded invariant
Reworking the `*_regime_mono` chain (`applyFnTClosure_regime_mono` 3012, `typecheckApp/Seq/If/
Vlet/Assign/Op/Deref/NewRef/UnaryOp/Var_regime_mono`, `typecheck_regime_mono_main` 3695 — all
delegated per-construct, IH-threaded) from `monotoneStep` to `monotoneStepExt` needs a
`monotoneStepExt` TRANSITIVITY lemma to compose the per-construct steps. Unlike the old
`regimeMonotone_trans` (TypeSafety:2552), `monotoneStepExt` transitivity is NOT derivable from the
relation alone: composing `R1→R2→R3` has the case `R2[k]=none` where step-2 could (per the relation)
re-add an old tag `k`; ruling that out (`R3[k]=none`) requires `k < step2.nextTag-floor`, i.e. a
**regime-domain-bounded invariant** `∀ k, R.lookup? k = some _ → k < nextTag`, which does NOT exist
in the codebase (grep confirms; `tagEnvBoundedInCtx` bounds tagEnv, not regime — they're disjoint).
The if-rule (mode-3) and the planned extern insertion both add guard tags `< nextTag'`, so the
invariant is TRUE and provable, but it is a NEW big induction (~13 cases mirroring
`typecheck_regime_mono_main`), and the chain must be reworked to a COMBINED conclusion
`(input regime bounded) → (monotoneStepExt … ∧ output regime bounded)`. The transport `_ext` lemmas
(StepFR) are UNAFFECTED — they discharge freshness from the VALUE's tag bound, not the regime's.
Sequence: (1) prove `typecheck_regime_bounded` (combined or standalone), (2) `monotoneStepExt_trans`
(taking regime-bounded), (3) rework `*_regime_mono` chain → `monotoneStepExt`, (4) insertion,
(5) `regime_monotoneExt` from the ext master + delete `regime_monotone`.

### Phase B — green foundation DONE (additive, full build green)
- `Regime.monotoneStepExt_refl`, `_weaken`, `_trans` (Typecheck.lean, in namespace Regime).
  `_trans` takes `hdisj : ∀ k, R1.lookup? k ≠ none → ¬ nt2 k` (supplied from regime-boundedness:
  old tags `< nextTag ≤` step-2 fresh floor) and yields `newTags = nt1 ∨ nt2` (weaken to `≥b1`).
- `applyExternRegimePolicy R id policy tagMapping` (Typecheck.lean, after `applyExternEffect`):
  folds `insert k b` over `tagMapping.toList` for `policy id k = some b`. The insertion fn itself.
- regime-boundedness is DERIVABLE (not a new induction): from `monotoneStep.2`/`monotoneStepExt.2`
  + nextTag-monotonicity + (fresh tags `< nextTag'`). So no separate big induction is needed;
  thread it as a derived fact in the chain rework.

### Phase B — DESIGN UPDATE: restricted-`.1` `monotoneStepExt` (eliminates regime-boundedness)
Redefine `monotoneStepExt`'s forward conjunct to be RESTRICTED to non-fresh tags:
`(∀ k b, ¬ newTags k → R.lookup? k = some b → (R'.lookup? k = some b ∨ R'.lookup? k = none)) ∧
 (∀ k, R'.lookup? k ≠ none → R.lookup? k ≠ none ∨ newTags k)`.
Consequences (all verified): `regime_monotoneExt` holds UNCONDITIONALLY (no regime-bounded hyp —
`¬newTags k` is exactly the no-collision condition); `monotoneStepExt_trans` needs NO `hdisj`
(the `R2[k]=none` case is closed by `¬nt2 k` from `¬(nt1∨nt2) k` + `mono2.2`);
`applyExternRegimePolicy_monotoneStepExt` needs NO `hfresh` (`¬newTags k ⇒ k∉tagMapping ⇒ R'[k]=R[k]`);
`monotoneStep_toExt` still trivial (ignores the new `¬newTags` arg) so leaf helpers `toExt` at the master.
**Step 0's `regimeBoundedInCtx`/`TagBoundedCtx`-extension is DROPPED entirely.** Keep ONLY the
`collectAndAllocExternTags` LOWER-bound lemma (`= .ok (tm,n') → tm.get? idx = some k → n ≤ k`), used to
`monotoneStepExt_weaken` the insertion's newTags up to `fun k => ctx.nextTag ≤ k`. Watch-points:
`locsRegime_monotoneExt`/`varsRegime_monotoneExt` gain a `¬newTags k` hyp (callers discharge via
`TagBoundedCtx_*` extractors); verify Phase D's StepFRApp BUILDS `inRegimeTrue` for the fresh tag
(does not push it forward through `.1`).

### Phase B — CASCADE CONFIRMED by a live trial (insertion wired then reverted)
Wiring `applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping` at the 4
simple-return sites (`Typecheck.lean`; rename `_id`→`id` in the 4 extern binders 1431/1503/1577/1646;
the 4 sites share the line `nextLoc' := nextLoc', nextTag' := nextTag', regime' := result2.regime' }`,
distinct from nested/non-extern → one `replace_all`) COMPILES in Typecheck.lean, and breaks TypeSafety
at exactly **4 errors**: the extern-`regimeMonotone_refl` sites in `applyFnTClosure_regime_mono`
(~3116) + `applyPFnTClosure_regime_mono` (~3169), and `applyFnTClosure_extern_regime_eq` (~4076, ~4147).
LEAF helpers (op/seq/if/vlet/assign/deref/newRef/unaryop/var_regime_mono) are UNCHANGED (no insertion
there → still monotoneStep; `toExt` at the master). So the chain rework is only:
`apply{Fn,PFn}TClosure(AtCursor)_regime_mono` + `applyFnTClosure_extern_regime_eq` + `typecheckApp_regime_mono`
+ `typecheck_regime_mono_main` (app case uses ext; other cases `toExt`) + `regime_monotoneExt` ← master.
Extern-simple case proof = `applyExternRegimePolicy_monotoneStepExt` (DONE) with
`hfresh : tagMapping tags ∉ result2.regime'` (from `result2.regime'` bounded + tagMapping tags ≥ result2.nextTag').
The composition (`monotoneStepExt_trans`) needs `hdisj` from the SAME boundedness.
**GENUINE BLOCKER = regime-domain-boundedness must be available.** Cleanest: add `regimeBoundedInCtx ctx
:= ∀ k, ctx.regime.lookup? k = some _ → k < ctx.nextTag` as a 4th conjunct of `TagBoundedCtx` (TypeSafety:~6440),
prove its preservation alongside the existing TagBoundedCtx preservation, and have the chain take it
(it's threaded in StepFRPost, so consumers get it free). A `collectAndAllocExternTags` lemma
(`tm.get? idx = some k → result2.nextTag' ≤ k`) supplies tagMapping-tag freshness. This boundedness
threading is the multi-hour core; everything else (transport `_ext`, algebra, insertion, extractors) is DONE.

### Phase B — REMAINING (red push, multi-session)
1. `applyExternRegimePolicy_monotoneStepExt R id policy tm (hfresh : ∀ idx k, tm.get? idx = some k →
   R.lookup? k = none) : monotoneStepExt R (applyExternRegimePolicy …) (fun k => ∃ idx, tm.get? idx = some k)`.
   Proof = fold lemmas: (A) `k ∉ tm-values → result[k] = R[k]`; (B) `result[k]≠none → R[k]≠none ∨ k∈tm-values`.
   `.1` uses hfresh (R[k]=some ⇒ k ∉ tm-values ⇒ (A)).
2. Wire insertion at the 12 extern result sites (`regime' := result2.regime'` →
   `applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping`); rename `_id`→`id` in the
   4 extern binders (applyFnTClosureAtCursor 1431, applyFnTClosure 1503, applyPFnTClosureAtCursor 1577,
   applyPFnTClosure 1646). THIS goes red (breaks `typecheck_regime_mono_main`).
3. Rework the `*_regime_mono` chain → `monotoneStepExt` (leaf cases: `(old monotoneStep).monotoneStep_toExt`;
   compound cases: `monotoneStepExt_trans` + `monotoneStepExt_weaken`; extern case: lemma 1). Helpers:
   applyFn/PFn(AtCursor)_regime_mono (3012-3197), typecheckApp/Op/Seq/NewRef/Assign/Deref/Vlet/If/UnaryOp/
   Var_regime_mono (3198-3600), typecheck_regime_mono_main (3695). IH type → monotoneStepExt.
4. `regime_monotoneExt` ← ext master; delete `regime_monotone`. → all ~90 consumers + transport calls +
   23 masked sites error → compiler-driven retargeting (parallel per-operator agents; freshness via the
   `TagBoundedCtx_*` extractors). Then Phase D (StepFRApp de-poisoning) + Phase E.

### Phase B — typechecker extern-tag insertion (Typecheck.lean) — details
After `collectAndAllocExternTags` (which yields fresh tags `[ctx.nextTag, nextTag')`), in:
`typecheckExternVal` (~932), `applyExternFnClosure` extern case (~1342/1414, the simple/nested
returns), and effect handling, query `ctx.externRegime id k` for each generated output tag `k`
attached to the returned value / effect-written cell, and `insert k ↦ b` into the produced
`regime'` when `some b`. Then re-prove `typecheck_regime_mono_main` (TypeSafety) directly as
`monotoneStepExt` (the extern app case now genuinely adds tags ≥ nextTag ⇒ satisfies
`fun k => ctx.nextTag ≤ k`). Producers (`_` newTags) auto-adapt; masked discharges now non-trivial
(use `hmasked_bounded`).

### Phase D — production-side two-run consistency (assumed boundary contract)
Add field to `ExternBoundarySpec` (ExternBoundary.lean:316), e.g.
`regimeFR : ExternCallBoundaryRegimeFR d impl`, stating: both runs share the typechecking
derivation (same concrete tag `k`); if `R(k)=true` both runs' extern value / written cell satisfy
the predicate (`qtypPredHolds`), if `R(k)=false` both fail. Consume in StepFRApp's extern case:
when the inserted tag has `R.lookup? k = some b`, build `valueConsistentWithRegime.inRegimeTrue`/
`inRegimeFalse` (reusing the existing `closureCapturedVarsRegime`, supplying `qtypPredHolds` from
`regimeFR`) instead of `notInRegime`. Mirror for effect-written cells (`locsRegime`/`consistentWithRegime`).
Provide `regimeFR` at `TrustedExternEntry` construction (trust). Update `TrustedRegistry.operationalSafe`-style
bridge if needed.

### Phase E — CLI + spec/docs
`Main.parseRegimeSpec`-style `--extern-regime "id=bool"` parse → install into
`TypeContext.externRegime` (id-only granularity: same bool for every output tag of that id).
Update `poison-lang-spec/poison-lang.ott` + `doc/poison-lang-description.tex`; add the `open`
acceptance example (§4.6) under `examples/`.

## Open-question dispositions
Q1 policy shape: `TypeContext` field (above). Q2 relation: `monotoneStepExt` (above).
Q3 dynamic domain bridge: derived from `monotoneStepExt` on demand (no separate threaded
invariant). Q4 production obligation: new `ExternBoundarySpec` field (assumed). Q5 masked:
freshness lemma (masked old, extern fresh). Q6 surfaces: concrete `StepFR` largely
unchanged except app extern case + monotone retarget. Q7 CLI multiplicity: v1 same-bool.

## FLIP IN PROGRESS (session breadcrumb — 2026-05-29)

State: atomic flip Steps 1→4 underway. Green backup tarball at
`/tmp/regime_flip_backup/green_baseline_*.tgz` (post-relocation green state; restore if flip must abort).

DONE & green-independent:
- `le_trans` ambiguity fix (Typecheck.lean:260 `_root_.le_trans`) — toolchain drift (`Std.le_trans` now exists).
- Step 0' relocation: regime-mono chain moved below `typecheck_nextTag_mono`; the 3 helpers
  (`TypecheckM_pure_eq`, `typecheckExternFn_ok_res_eq`, `typecheckExternPfn_ok_res_eq`) kept ABOVE the
  nextTag chain (they're used by it). `collectAndAllocExternTags_mapping_values_ge` (lower bound) already exists.
- Step 1 insertion wired (4 simple-return sites use `applyExternRegimePolicy result2.regime' id ctx.externRegime tagMapping`).

RED now: TypeSafety (4-error cascade as predicted: 2× `*_extern_field_eq_aux` regime conjunct, 2× `*_regime_mono` extern simple).

DESIGN (validated against all 7 `extern_regime_eq` consumers):
- Unifying lemma `applyFnTClosure_extern_regime_eq_or_policy (happly) :
  r2.regime' = r1.regime' ∨ ∃ tm, r2.regime' = applyExternRegimePolicy r1.regime' id ctx.externRegime tm
  ∧ (∀ idx j, tm.get? idx = some j → r1.nextTag' ≤ j)` (+ PFn + AtCursor). Serves BOTH the chain
  (Right→`applyExternRegimePolicy_monotoneStepExt` weakened to `≥ r1.nextTag'`; Left→refl) AND consumers
  (`extern_regime_old_eq (k) (hk:k<r1.nextTag') : r2.regime'.lookup? k = r1.regime'.lookup? k`).
- `*_extern_field_eq_aux`: drop the regime conjunct (tagEnv/memEnv stay; those ARE still rfl). Delete `extern_regime_eq`.
- Consistency consumers (regimeConsistentWithCtx[Masked]) use wrappers (ADD to RegimeConsistency, after the defs):
  `tagEnvConsistentWithRegime[Masked]_of_old_eq (hcons)(htb: tagEnvBounded te bound)(hold: ∀k<bound, R2[k]=R1[k]) : ... R2`.
  `htb` sourced from `TagBoundedCtx.tagEnvBoundedInCtx` (threaded in StepFRPost). Specific-tag consumers
  (StepFR:14330, TypeSafety:16174) use `extern_regime_old_eq` directly with a local `k<nextTag'` bound.
- Chain rework: leaf→`.monotoneStep_toExt`; compound→`monotoneStepExt_trans_le ... (typecheck_nextTag_mono)`;
  extern→`_eq_or_policy`. `regime_monotoneExt`←ext master; delete `regime_monotone`.

## KEY DESIGN PIVOT (2026-05-29): insert-if-absent applyExternRegimePolicy
Exact-preservation lemmas (`= some b`, no-drop-no-overwrite) — esp.
`typecheckExpr_pure_regime_bridge_of_toPExpr` (14 consumers) and the `regimeConsistentWithCtx`
preservation consumers — broke at the extern-insertion case (an old regime tag could be overwritten by a
fresh extern tag), which would have required reintroducing regime-boundedness threading through 14 sites.
RESOLVED by making `applyExternRegimePolicy` INSERT-IF-ABSENT (only insert when `R.lookup? p.2 = none`).
Then "existing entries preserved exactly" holds definitionally:
`applyExternRegimePolicy_lookup_preserve_some : R.lookup? k = some b → result.lookup? k = some b` is
UNCONDITIONAL (no k-bound). Observationally identical (extern tags are freshly allocated, never already in R).
Blast radius: def + `applyExternRegimePolicy_lookup_spec` (re-proved) + `_monotoneStepExt` (easier).
Replaces `extern_regime_old_eq` (needed k<nextTag) with `extern_regime_preserve_some` (Fn/PFn, unconditional);
DROPS the planned `tagEnvConsistentWithRegime_of_old_eq` wrappers + tagEnvBounded threading entirely.
Consistency consumers now: tagEnv_eq + preserve_some on the (true) regime entry from hcons.

## STEP 3 PROGRESS (2026-05-29, session 2)
TypeSafety GREEN (full monotoneStepExt chain; regime_monotone deleted; regime_monotoneExt master;
eq_or_policy + preserve_some lemmas; insert-if-absent applyExternRegimePolicy). StepFR down 54→3 errors.
DONE in StepFR: masked framework `typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv_main` threaded
`hmasked_bounded : ∀k, masked k → k < ctx.nextTag` (input+output, all cases: op/seq/vlet/assign/deref/
newRef/if-true/if-false/if-std/app + closure bodies); wrapper got the new hyp (→ 17 consumers in other
files will need it supplied — vacuous at top FaultRobustnessProofs where masked=False). Added
`applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound` (tag analog of the Loc one) +
made `apply{Fn,PFn}TClosureAtCursor_nextTag_advance` public for closure-body bounds. masked-consistency
consumers (regimeConsistentWithCtxMasked) reworked via tagEnv_eq + preserve_some.
REMAINING StepFR (3 errors, all in `typecheckExpr_lookup_origin_of_pc_true_split` ~13364, backward-trace
under pc=true): need `k < cursor.1` (k = a memEnv guard tag) to run the BACKWARD regime step
(`srcRes.regime'[k]=true → rCursor.regime'[k]=true`). 14539: regular-closure passes regime_monotone as IH
→ regime_monotoneExt + monotoneStepExt_lookup_back (needs ¬newTags k = k<cursor.1). 14446/14563: extern
backward → need a backward preserve lemma with k<r1.nextTag'. The bound k<cursor.1 needs TagBoundedCtx
(memEnv guardTag bound, `TagBoundedCtx_memEnv_guardTag_lt`) threaded through this lemma (it currently only
has hwf=wfTypeContext which bounds LOCS not tags). THIS is the next invasive bit.
PATTERN: each downstream backward/exact-regime site needs a tag bound the local lemma lacks.

## STEP 3 — backward-trace lemma threading (VERIFIED TEMPLATE, in progress)
`typecheckExpr_lookup_origin_of_pc_true_split` (StepFR ~13364): added `(hbnd : TagBoundedCtx ctx)` hyp
(reverted + intro'd). 32 `ih` calls need it. VERIFIED TEMPLATE (op case, compiles):
- e1-at-ctx calls (22): replace_all ` hwf hpc l ` → ` hwf hbnd hpc l ` (DONE).
- sub-context calls (~10): add parallel `have hbnd_<x> : TagBoundedCtx <subctx> := by
  simpa [<subctx-defn>, ctxAfter] using typecheckExpr_preserves_TagBoundedCtx ctx <e> (fuel'-1) <result>
  (by simpa using <htc>) hbnd` next to the existing `hwf_<x>`, then insert `hbnd_<x>` after `hwf_<x>` in
  the ih call. DONE: op (hbnd_ucr). PENDING: seq(13546)/vlet(13590)/assign(13819)/ite-true(13854)/
  ite-false/ite-std(13929,13948,13975,13996)/app-ctxFun(14040,14061).
- CLOSURE-BODY calls (14184,14414): bodyCtx (captured env, nextTag=cursor.1). Needs TagBoundedCtx bodyCtx
  = the TAG analog of the existing loc-bound derivation (14153-14180) using CapturedEnvFullBounded/
  ofCaptured_* + the function-result closureEnvBoundedInCtx (via hbnd_ctxFun). ~30 lines each. This is the
  one genuine (non-mechanical) sub-derivation in this lemma.
- Then the 3 ORIGINAL backward sites: 14539 regular-closure (regime_monotone→regime_monotoneExt IH; then
  monotoneStep_lookup_back→monotoneStepExt_lookup_back with `k<cursor.1` from TagBoundedCtx_memEnv_guardTag_lt
  on the result1 memEnv bound — derive predTagsBoundedInMemEnv result1 via typecheckExpr_preserves_predTagsBounded
  through e2,e1 from hbnd). 14446/14563 extern backward: add `applyFnTClosure/PFn_extern_regime_preserve_some_back
  (k<r1.nextTag') : r2.regime'[k]=some b → r1.regime'[k]=some b` (eq_or_policy + lookup_spec + mapping_values_ge
  contradiction), apply with k<cursor.1.
- 2 consumers of this lemma (StepFR 14613, 14633) supply hbnd from TagBoundedCtx in StepFRPost scope.

## OVERALL STATUS (honest)
DONE GREEN: relocation, le_trans fix, Typecheck insertion, TypeSafety FULL monotoneStepExt chain rework
(the hard conceptual part). StepFR: masked framework + closure-body cursor bound + masked-consistency
consumers DONE; backward-trace lemma threading ~50% (template verified, ~13 sub-contexts + closure-body + 3
sites remain). REMAINING after StepFR: StepFRApp (~56 producers, same 4 patterns: preserve_some/
hmasked_bounded/cursor-tag-bound/TagBoundedCtx-for-old-tags) + other per-op files + 17 wrapper consumers
supply hmasked_bounded (vacuous where masked=False) + Phase D (ExternBoundarySpec.regimeFR + StepFRApp
de-poisoning by-cases) + Phase E (CLI/Ott/tex/example). Genuinely multi-session. Backup tarball:
/tmp/regime_flip_backup/green_baseline_*.tgz (post-relocation green floor).

## STEP 3 backward-trace lemma — DONE (StepFR GREEN, 7760 jobs)
typecheckExpr_lookup_origin_of_pc_true_split: hbnd:TagBoundedCtx threaded through op/seq/vlet/assign/
ite-true/ite-false/ite-std/app-ctxFun (ALL done & compiling). Helpers used: typecheckExpr_preserves_TagBoundedCtx,
typecheckExpr_TagBoundedCtx_varEnv_update (vlet), matchGuard_tag_bounded + tagEnvBounded_insert_of_lt (ite-true/false),
tagEnvBounded_mono/predTagsBoundedInVarEnv_mono/predTagsBoundedInMemEnv_mono/varEnvClosuresCapturedBounded_mono (ite-false/std/E3).
REMAINING (≈5 errors):
1. CLOSURE-BODY bodyCtx (2 sites, ~14229 Fn / ~14459 PFn): need TagBoundedCtx bodyCtx (captured env tenv,
   nextTag=cursor.1). Recipe = TAG analog of the existing loc-bound hwf_bodyCtx proof (14201-14228):
   - need cursor.1 ≥ result1.nextTag': the current rcases uses loc-only
     `applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bound`. ADD a combined tag+loc variant
     (generalize my `..._with_cursor_tag_bound` + the loc one to thread BOTH baseTag/baseLoc) and use it
     (rcases pattern gains hcursorTag) — OR derive cursor.1≥result1.nextTag' separately.
   - construct ⟨tagEnvBounded_mono <result1 tagEnv bound> ≤cursor.1, ⟨predTagsBoundedInVarEnv_update
     (predTagsBoundedInVarEnv_ofCaptured (capturedPredTagsBounded_of_fullBounded (CapturedEnvFullBounded_mono
     <tenv tag bound from e1 result etypClosuresFullBounded member> ≤cursor.1))) <inserted var ⟨etyp2,_,pred2⟩
     qtypPredTagBounded cursor.1>, predTagsBoundedInMemEnv_mono <result1 memEnv> ≤cursor.1⟩,
     varEnvClosuresCapturedBounded_update (varEnvClosuresCapturedBounded_ofCaptured (CapturedEnvFullBounded_mono...))
     <etyp2 closures>⟩. Need a PUBLIC accessor for `(preserves_combined_main).2.2 = etypClosuresFullBounded
     result1.qualType.etyp result1.nextTag'` (combined_main is private — add thin public wrapper in TypeSafety).
2. 3 BACKWARD sites (~14492 extern-Fn / ~14585 regular-PFn / ~14609 extern-PFn): after bodyCtx threading,
   hbnd is in scope. 14585 regular: replace `regime_monotone` IH → `regime_monotoneExt`; then
   monotoneStep_lookup_back → monotoneStepExt_lookup_back with `¬newTags k = k<cursor.1` from the memEnv bound
   (predTagsBoundedInMemEnv result1.memEnv' result1.nextTag' via preservation from hbnd_ctxFun → k<result1.nextTag'≤cursor.1).
   14492/14609 extern: add `applyFn/PFnTClosure_extern_regime_preserve_some_back (k<r1.nextTag') :
   r2.regime'[k]=some b → r1.regime'[k]=some b` (eq_or_policy: Left→h; Right→lookup_spec, ∃idx case gives
   k≥r1.nextTag' via mapping_values_ge, contradict) and apply.
3. 2 CONSUMERS (~14660/14680/14699 region): supply `hbnd` arg = TagBoundedCtx from StepFRPost scope.

## MILESTONE: StepFR GREEN (session 2). Downstream wave precisely scoped.
TypeSafety + StepFR both GREEN. Full build reaches 10822/10839; StepFRApp/Deref/NewRef/Literal/Var/FnPfn
ALL built. Added in TypeSafety: typecheckExpr_preserves_qualType_closures_bounded (public accessor),
applyFn/PFnTClosure_extern_regime_preserve_some_back (backward, k<r1.nextTag'). Added in StepFR:
applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_bounds (combined tag+loc) + the tag-only one.
The 4 pc-true wrappers (typecheckExpr_lookup_{poison,guard}_origin/clean_lookup_origin/lookup_clean_back)
now take (hbnd : TagBoundedCtx ctx).

REMAINING WAVE — 5 maskedReg per-operator files (StepFROp 8 / Vlet 7 / Seq 7 / Assign 6 / Ite 5) +
ExternBoundaryProofs 1. SAME patterns in each `stepFRSingleRunFinalCleanPcTrue_<op>_maskedReg_with_expr_proof`:
  (a) `regime_monotone ctx e fuel res htc'` → `regime_monotoneExt ...` (type monotoneStepExt ... (fun k=>ctx.nextTag≤k)).
  (b) `masked_lookup_none_of_monotoneStep hmasked_none hmono k hk` →
      `masked_lookup_none_of_monotoneStepExt hmasked_none (fun t ht => Nat.not_le.2 (hmasked_bounded t ht)) hmono k hk`.
  (c) `typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv masked ctx e fuel res habsent hmasked_none htc`
      → add `hmasked_bounded` arg before htc.
  (d) `typecheckExpr_clean_lookup_origin_of_pc_true hExtTyping (ctx:=..) .. htc hwf <hpc> l qt ..` → insert
      `hbnd` (TagBoundedCtx of that ctx) after hwf.
THE THREADING: `StepFRSingleRunFinalCleanPcTrueMaskedRegParam` (StepFR:1111) + its Post + IH need TWO new
threaded hyps: `(hmasked_bounded : ∀ k, masked k → k < ctx.nextTag)` and `(hbnd : TagBoundedCtx ctx)`,
added after hmasked_absent (line 1133). Then the 6 per-operator maskedReg lemmas (op/seq/vlet/assign/ite +
the IH `..._IH_WithExprCtx`) intro them and re-establish for sub-contexts (ctx' = updateCtxFromResult:
hmasked_bounded via Nat.lt_of_lt_of_le + typecheck_nextTag_mono; hbnd via typecheckExpr_preserves_TagBoundedCtx).
Dispatch in FaultRobustnessProofs supplies both: hmasked_bounded discharged `fun k hk => absurd hk id`
(masked≡fun _=>False at top, FaultRobustnessProofs:~2203); hbnd from the StepFRPost TagBoundedCtx already in scope.
ExternBoundaryProofs:1 — likely a regime_monotone or extern_regime_eq site (same fix).
AFTER WAVE: FaultRobustnessProofs (orchestration, may need the 2 new args at maskedReg dispatch) → full green.
THEN Phase D (ExternBoundarySpec.regimeFR + StepFRApp de-poisoning by-cases on R.lookup? k=some b) + Phase E.

## SESSION 2 END — 5 files GREEN; maskedReg framework threaded; two-run recipe nailed.
GREEN: TypeSafety, StepFR, StepFRApp, StepFROp, StepFRSeq (+ Deref/NewRef/Literal/Var/FnPfn from before).
maskedReg framework: StepFRSingleRunFinalCleanPcTrueMaskedRegParam (StepFR:1111) + Post (1037) gained
`(hmasked_bounded : ∀k,masked k→k<ctx.nextTag)` and `(hbnd : TagBoundedCtx ctx)` after hmasked_absent.
Per-operator maskedReg lemmas threaded (op/unaryop/seq/assign/vlet DONE; recipe = intro both hyps; IH
applications supply them (top-ctx: hmasked_bounded hbnd; sub-ctx: hmasked_bounded1'/hbnd1' via
typecheck_nextTag_mono + typecheckExpr_preserves_TagBoundedCtx / typecheckExpr_TagBoundedCtx_varEnv_update);
regime_monotone→regime_monotoneExt; masked_lookup_none_of_monotoneStep→_of_monotoneStepExt
(fresh = fun t ht => Nat.not_le.2 (hmasked_bounded t ht)); typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv
+hmasked_bounded; clean_lookup_origin +hbnd1). StepFROp/Seq build green via this.

REMAINING — TWO-RUN consistency proofs (stepFR_<op>_with_expr_proof). KEY: the StepFR two-run framework
(StepFR.lean:334, `def StepFR`) ALREADY provides `TagBoundedCtx ctx` (line 349) — so backward uses are
MECHANICAL. Pattern (per assign/ite/vlet agent analysis):
  - regime_monotone → regime_monotoneExt.
  - BACKWARD `.2` (`R'[k]≠none→R[k]≠none`) / `monotoneStep_lookup_back` (`R'[k]=some b→R[k]=some b`):
    under monotoneStepExt these need `¬newTags k = k<ctx.nextTag`. k is a memEnv/varEnv cell guard tag →
    discharge `k<ctx.nextTag` via `TagBoundedCtx_memEnv_guardTag_lt htag <cell-lookup> <guardTag>` (or varEnv
    variant) on the in-scope TagBoundedCtx, then `Nat.not_le.2`, then `monotoneStepExt_lookup_back`/`.2`.
    EXACT TEMPLATE already in StepFR.lean lines 5176-5209 (the consistentWithRegime transport helper).
  - FORWARD `.1` + `qtypCleanUnder_of_monotone` port cleanly to the ext forward conjunct.
  Sites: ASSIGN stepFR_assign_with_expr_proof (regime_monotone @2180,2284→hmono12; backward `.2` @2488,2606,
  2757,2876,3153; forward `.1` @2612,2814,3210; qtypCleanUnder @3268). ITE (hmono2 @~3566; lookup_back @4120,4834
  in hlookup_back_final_to_res1; thread the bound into that ∀k helper from TagBoundedCtx). VLET (uses @1074,
  1202-1207,1264-1266,1339-1341,1400-1402; ADDITIONALLY needs Ext transports `memberCvcrEvidence_monotoneExt`
  and an Ext form of `agreeValueUnder_clean_transport_by_cleanBack` — ADD to StepFR.lean, mirroring the
  existing `memberVarsRegimeEvidence_monotoneExt`/`cleanUnder_of_monotoneExt`).
THEN: ExternBoundaryProofs (1 err), FaultRobustnessProofs (orchestration — maskedReg dispatch supplies the 2
new hyps: hmasked_bounded `fun k hk=>absurd hk id` where masked≡False, hbnd from StepFRPost TagBoundedCtx),
Phase D, Phase E. 0 sorry/0 axiom maintained throughout.

## SESSION 3 END — shared Ext engine landed; App is the big remaining piece

GREEN now (0 sorry/0 axiom): TypeSafety, StepFR, StepFROp/Seq/Assign/Vlet/Ite, ExternBoundary,
ExternBoundaryProofs.

NEW shared lemmas added to StepFR.lean (the conceptually hard part, DONE):
- `memberCvcrEvidence_monotoneExt` (after memberVarsRegimeEvidence_monotoneExt): mirrors the
  non-Ext via `closureCapturedVarsRegime_monotoneExt` + `etypClosuresFullBounded_of_ofCaptured_lookup`.
- `agreeValueUnder_clean_transport_by_cleanBack_ext` (after monotoneStep_lookup_back): clones the
  non-Ext `.rec` engine; threads `etypClosuresFullBounded qt.etyp B` (motive_1) and
  `CapturedEnvFullBounded σcap B` (motive_2); arrow/parrow cases extract per-closure bound via
  `rw [hetyp]; hb tcl htcl; rw [hmatch]`; cons cases split head (`CapturedEnvFullBounded_member_etypClosures`)
  / tail (`CapturedEnvFullBounded_tail`); cons_dirty cleanBack via `cleanUnder_of_monotoneExt`.
  DROPPED `h_clean_back` + 4 transport hyps (all derived internally). Sig: (h_mono)(hnewB)(hbound).
TypeSafety.lean public helpers added (after varEnvClosuresCapturedBounded_ofCaptured):
  `CapturedEnvFullBounded_member_predTagBounded`, `CapturedEnvFullBounded_tail`,
  `etypClosuresFullBounded_of_ofCaptured_lookup`.
Vlet sorry@1099 REMOVED: forward transport via the new engine (h_mono_e2, fun _ hk=>hk,
  etypClosuresFullBounded_mono(TagBoundedCtx_varEnv_etypClosures …) hbge1, hclean_final, _hagree_val).
Ite divergent cluster: hmono2→Ext + composed h_mono_final (monotoneStepExt res1.regime' res.regime'
  floor res1.nextTag', via monotoneStepExt_trans_monotoneStep + joinRegimes_lookup_some_left);
  var-case engine call → _ext; deleted hlookup_back_final_to_res1 + 4 transports in both blocks.
ExternBoundary/Proofs: threaded the 2 new Post args (`hmasked_bounded : ∀k, masked k→k<ctx.nextTag`,
  `hbnd : TagBoundedCtx ctx`) through `to_maskedRegParamPost`, `ExternDeclBoundarySingleMaskedContract`(+
  `.of_spec`, `.of_trustedReachable`). FIXED proof-local `fnExternFinishAtCursor` (ExternBoundaryProofs:1597):
  added `(id : ExternId)` param + applied policy in the SIMPLE case only (matching real
  applyFnTClosureAtCursor:1482; nestedFn/nestedPfn keep result2.regime').

REMAINING:
1. StepFRApp.lean — 78 errors (was NEVER actually green; App proof sites never updated). Categories:
   a. `regime_monotone`→`regime_monotoneExt` (gives monotoneStepExt floor ctx'.nextTag; `by simpa
      [ctxAfter] using regime_monotoneExt ctx' e m res' htc`). Sites ~2789,2871,6091,6111,6253,8720,8763,8958.
   b. App-local `applyFnClosuresThreaded_join_regime_mono`(2758) / `applyPFnClosuresThreaded_join_regime_mono`
      (2840): conclude `monotoneStepExt result1.regime' res.regime' (fun k=>result1.nextTag'≤k)`. Members via
      `applyFnTClosureAtCursor_regime_mono` give floor cursor.1 → unify to result1.nextTag' with
      `monotoneStepExt_weaken … (fun k hk => Nat.le_trans <result1.nextTag'≤cursor.1> hk)`; combine via
      `joinTypeResults_regime_monotone` (NOW Ext: takes monotoneStepExt R r.regime'/x.regime' newTags).
   c. `applyFnTClosure_extern_regime_eq`→`applyFnTClosure_extern_regime_eq_or_policy` (1415) and PFn (1878):
      now returns `r2.regime'=r1.regime' ∨ ∃tm, r2.regime'=applyExternRegimePolicy r1.regime' id ctx.externRegime
      tm ∧ (∀idx j, tm.get? idx=some j→r1.nextTag'≤j)`. rcases; SAME branch as before; POLICY branch:
      for regimeConsistentWithCtx preservation use `applyExternRegimePolicy_lookup_preserve_some r1.regime' id
      ctx.externRegime tm k true (hreg1 k deps hget)` (insert-if-absent preserves existing trues, UNCONDITIONAL);
      for monotone use `applyExternRegimePolicy_monotoneStepExt`. tagEnv is UNCHANGED by policy.
   d. MaskedRegParamPost Post-helper lemmas (conclusions @5630,5728,5832; also 8699,9215,9691 etc.): add params
      `(hmasked_bounded : ∀k, masked k→k<ctx.nextTag)` + `(hbnd : TagBoundedCtx ctx)` after hmasked_absent and
      insert them in the Post application (before hctxCons). Same pattern as ExternBoundary.
   API (TypeSafety): applyFnTClosureAtCursor_regime_mono(5387, Ext floor cursor.1), applyPFn…(5410),
   applyFnTClosure_regime_mono(5308, floor r1.nextTag'), joinTypeResults_regime_monotone(4966, Ext),
   applyFnTClosure_extern_regime_eq_or_policy(5215), applyExternRegimePolicy_monotoneStepExt(5134),
   applyExternRegimePolicy_lookup_preserve_some(5096), regime_monotoneExt(6086).
   (Typecheck) monotoneStepExt_weaken(221), monotoneStepExt_trans_le(255), monotoneStepExt_trans(229).
2. FaultRobustnessProofs.lean — orchestration: the masked dispatch supplies the 2 new Post hyps. masked≡False
   at top, so hmasked_bounded := `fun k hk => absurd hk id`/`(nomatch hk)`; hbnd from the StepFRPost
   TagBoundedCtx. Contract type refs @430,2190,2370 + `.of_trustedReachable`@2952.
3. Progress.lean / MemoryMonotonicity.lean — rebuild to check (likely unaffected; verify).
4. Phase D (production two-run via ExternBoundarySpec.regimeFR) + Phase E (CLI/docs/example) — not started.

## SESSION 4 — StepFRApp partial retarget (≈78 → ≈46 errors; DONE clusters durable)

DONE & in-file (all sound, verified by JoinMemberTransport compiling green):
- Category C: `applyFnTClosure(_+PFn)_extern_regime_eq` → `_eq_or_policy` rcases (Fn ~1415, PFn ~1884).
  Policy branch: `applyExternRegimePolicy_lookup_preserve_some result1.regime' id ctx.externRegime tm k true (hreg1' k deps hget)`.
- Category B: App-local `apply{Fn,PFn}ClosuresThreaded_join_regime_mono` (~2770/~2870) now conclude
  `monotoneStepExt result1.regime' res.regime' (fun k=>result1.nextTag'≤k)` via
  `applyClosuresThreaded_ok_mem_output_exists_input_with_cursor_tag_bound` (base result1.nextTag') +
  per-member `monotoneStepExt_weaken (apply*AtCursor_regime_mono … regime_monotoneExt) (fun k hk=>Nat.le_trans hcur hk)`
  + `joinTypeResults_regime_monotone` (Ext).
- Category A IH-lambdas: `by simpa [ctxAfter] using regime_monotone …` → `regime_monotoneExt` (7 sites).
- Category D Post-helpers: `appSingleRunMaskedPost_from_body_fields` (×3) + the two top maskedReg `intro`s +
  the e2-IH application sites gained `hmasked_bounded`/`hbnd` after `hmasked_absent`.
- masked dispatch e2/e1 blocks (×8 each): `hmono2`/`hmono1` → monotoneStepExt; added `hmasked_bounded2`/`hbnd2`
  (+`hmasked_bounded1`/`hbnd1`); `masked_lookup_none_of_monotoneStep`→`_of_monotoneStepExt` (freshness
  `fun t ht=>Nat.not_le.2 (hmasked_bounded* t ht)`); `typecheckExpr_preserves_MaskedTagsAbsentFromTrueTagEnv`
  gained `hmasked_bounded*` arg.
- **Body-start family (the big sound restructure):** the 4 defs (`App{,Extern}{,P}ClosureBodyStart`) hmono →
  `monotoneStepExt … (fun k=>(ctxAfter ctx result2).nextTag≤k)` + 2 new hyps
  `qtypPredTagBounded result2.qualType …` / `etypClosuresFullBounded result2.qualType.etyp …`; the 4
  `consistentWithRegimeMasked_app_*_body_start` lemmas + 6 providers + all body-start invocation sites
  threaded those bounds; internal `valueConsistentWithRegimeMasked_monotone`/`closureCapturedVarsRegimeMasked_monotone`
  → `_monotoneExt` (`(fun _ hk=>hk)` + `simpa [qtypPredTagBounded?, hqt2] using hqt2bound/hetyp2bound`).
- **Two-run h_mono1 (12 local defs):** all → monotoneStepExt; `hqt2bound1`/`hetyp2bound1` HOISTED once per
  branch right after each `intro` (arrow ~11561, parrow ~16937); regular body-start invocations +
  `valueConsistentWithRegime_monotone`/`closureCapturedVarsRegime_monotone` → `_monotoneExt`;
  `cleanUnder_of_monotone`/`agreeValueUnder_clean_monotoneRegime` → Ext.
- **NEW shared lemma** `agreeValueUnder_clean_monotoneRegime_ext` added to JoinMemberTransport.lean (green).
- Sub-context `typecheckExpr_lookup_clean_back_of_pc_true` calls (`hwf2 hpc2`→`hwf2 hbnd2 hpc2`, 7 sites).

RESIDUAL (≈46 errors, ALL one of three SOUND restructures — none need Phase D except possibly the appMember
universal; advisor says even that is inherited-cell restructure-able via `typecheckExpr_lookup_clean_back_of_pc_true`):
A. **Closure-body `TagBoundedCtx bodyCtx` derivation MISSING** (the one genuinely non-mechanical ~30-line piece,
   green precedent = StepFR `typecheckExpr_lookup_origin_of_pc_true_split` closure-body block via public
   accessors `typecheckExpr_preserves_qualType_closures_bounded`/`CapturedEnvFullBounded_member_*`). Unblocks:
   `clean_back_of_pc_true` bodyCtx sites (6289/9642/12827/14716/20260; paired `hlookup*` "expected QTyp"
   cascades clear with it) + the `hcwr_body` masked body single-run calls (9039/10452, which also need
   `hmasked_bounded_body hbnd_body`).
B. **Backward cluster (sound, inherited/old cells):** `regime_lookup_back_of_monotone` local lemma (~4790) +
   the `have hmono : monotoneStep := apply*AtCursor_regime_mono …` defs (6161/6181/6323/16705/18232/22216) +
   `applyFnTClosure_staticSource_of_threaded_mem` conclusion (~6062/6293 PFn): restate the backward `regime` field
   `OLD-k-only` (`k<r1.nextTag'`) and route through `monotoneStepExt_lookup_back` (freshness from inherited
   memEnv-cell tag bound `< cursor.1`, exactly StepFR's split-lemma pattern). The local `h_mono_bodyA*` defs
   (12536/12538/13631/… `regime_monotone bodyCtx*`) likewise → `regime_monotoneExt` then backward via the bound.
C. **Join consumers + appMember** (14213/14891/15553/18239/19814/20440/21057 `applyFn/PFnClosuresThreaded_join_regime_mono`
   into `hpre_to_res_mono`, and the inline `joinTypeResults_regime_monotone` at 12685/18239): the join lemma now
   gives monotoneStepExt; `appTwoRunOutChoice_from_independent_single_posts_{dirty,clean}` (~8210/~8500)'s
   `hpre_to_res_mono : monotoneStep preCtx.regime (ctxAfter ctx res).regime` + its `h_clean_res_to_pre` (8358,
   backward clean over ALL res memEnv cells) is the ONE site to VERIFY with lean_goal: its some-case
   (`l∈preCtx.memEnv`) is inherited⇒restructure via `typecheckExpr_lookup_clean_back_of_pc_true`; only if a
   touched cell can be policy-set-true (fresh) is it genuine Phase-D (regimeFR). NOT yet verified.
NOTE: 4 `Unknown identifier agreeValueUnder_clean_monotoneRegime_ext` errors in StepFRApp are LSP staleness
(JoinMemberTransport not re-elaborated by the in-process LSP); they resolve on a real `lake build`.

## SESSION 3 (cont.) — StepFRApp ground truth + grinding recipe (advisor-blessed)

REAL-BUILD STATUS (env LAKE_NO_CACHE not needed; plain `lake build LeanProofs.X`):
GREEN (0 err, 0 sorry, 0 axiom): TypeSafety, StepFR, StepFROp, StepFRSeq, StepFRAssign, StepFRVlet,
StepFRIte, ExternBoundary, ExternBoundaryProofs, JoinMemberTransport.
RED: StepFRApp = 49 errors (real build; lean-lsp is UNRELIABLE here — stale oleans hid the count and
the `agreeValueUnder_clean_monotoneRegime_ext` "unknown id" false positives; ALWAYS verify StepFRApp with a
real `lake build`, NOT lean-lsp). Error mix: 16 Application-type-mismatch, 11 Function-expected, 8
`regime_monotone` unknown-id, 5 Type-mismatch, 5 `simp made no progress`, 3 after-simp, 1 unknown
`hσcap₀_mem`.

ADVISOR DECISION: do NOT dispatch more subagents to StepFRApp (they can't `lake build`, verify via stale
lean-lsp, and REGRESS — two passes went 78→46→49 + injected breakage). GRIND IT YOURSELF with a real
`lake build` after each cluster (count must drop monotonically). StepFRApp is an import LEAF (only
FaultRobustnessProofs imports it) → broken state cannot threaten the 10 green files; safe to grind across
windows. Do NOT revert the 2nd agent's work — its shared-interface→Ext migration is load-bearing; the
46→49 rise is mostly UNMASKED leaf errors (one elaboration failure per block had hidden its siblings).

ROOT CAUSE (settled): under monotoneStepExt the app body inserts FRESH extern tags k≥result1.nextTag', so
the old full backward lookup `∀ k b, src.regime'[k]=some b → result1.regime'[k]=some b` is GENUINELY FALSE
and cannot be built at any leaf. Every consumer must instead take `monotoneStepExt … (fun k=>preCtx.nextTag≤k)`
+ `TagBoundedCtx` and discharge the fresh disjunct at the (bounded) guard tags of varEnv/memEnv/captured
cells via `monotoneStepExt_lookup_back` / `.2`-rcases + `TagBoundedCtx_{mem,var}Env_guardTag_lt`.

KEY REUSABLE INFRA ALREADY GREEN in StepFRApp:
- `tagBoundedCtx_closure_body` (def ~2179): GIVEN (ctxᵢ result2 result1 e1 e2 fuel' σcap etyp2 p2 pred2 pcBody
  pureCtxBody cursor x) (htc1' htc2' hqt2) (hCapBoundBase : CapturedEnvFullBounded σcap result1.nextTag')
  (hbnd : TagBoundedCtx ctxᵢ) (hbnd1 : TagBoundedCtx (ctxAfter (ctxAfter ctxᵢ result2) result1))
  (hcursorTag : result1.nextTag' ≤ cursor.1) PRODUCES `TagBoundedCtx {ctxᵢ with pc:=pcBody, pureCtx:=
  pureCtxBody, memEnv:=result1.memEnv', varEnv:=update (ofCaptured σcap) x ⟨etyp2,joinPoison ctxᵢ.pc p2,
  pred2⟩, tagEnv:=result1.tagEnv', nextTag:=cursor.1, nextLoc:=cursor.2, regime:=result1.regime'}`. Use it
  at every bodyCtx site to get `TagBoundedCtx bodyCtxX`. (hCapBoundBase via
  `typecheckExpr_preserves_closureCapturedBounded (ctxAfter ctxᵢ result2) e1 fuel' result1 … _htagBounded2.2.1
  _htagBounded2.2.2`, then `rw [hetyp1]`, then `hClosFull <the tcl> <tcl∈tcls membership>` — precedent at
  ~13036/13045; the membership is the closure's `… ∈ tcls`, NOT a fresh name).
- New shared lemma `agreeValueUnder_clean_monotoneRegime_ext` in JoinMemberTransport.lean (green).

CONSUMER-THREADING RECIPE (the 49 errors are this, replayed across symmetric fn/pfn × U/E × ₀/₁ blocks):
1. `simp made no progress` (15618,16223,17037-38,22572) + Function-expected (11): consumer call sites of
   `applyFn/PFnTClosure_staticSource_clean_back_of_p1p_true` and the `hlookupBack*`/join consumers were NOT
   updated to the producer's NEW Ext signature. The producer `applyFnTClosure_staticSource_clean_back_of_p1p_true`
   (def 6304) now takes, after `hp1p`: `(hlookupBack : monotoneStepExt bodyState.regime' first.regime'
   (fun k=>bodyState.nextTag'≤k))` `(hmemGuardBnd : ∀ l qt k, bodyState.memEnv'.lookup l=some qt →
   qtypGuardTag qt=some k → k<bodyState.nextTag')` `(hbodyCtx_mem)` `(hbodyCtx_regime)` `(hbodyCtx_pc)`
   `(hbnd_body : TagBoundedCtx bodyCtx)` `(hwfBody)`. So each consumer must supply hmemGuardBnd (from
   `TagBoundedCtx bodyCtx` via `TagBoundedCtx_memEnv_guardTag_lt`, but note hmemGuardBnd is over
   bodyState.memEnv' = bodyCtx.memEnv) AND hbnd_body (via tagBoundedCtx_closure_body). "Function expected"
   = a site applying a now-`monotoneStepExt` value `hlookupBackX k b hk` as if it were the old ∀-function;
   replace with the backward discharge.
2. `regime_monotone` ×8 (12536,12538,13631,13844,14029,14687,15365,16716,18059,18061,19152,19384,19594,
   20231,20857 — the leftover backward-cluster `h_mono_body*`): `regime_monotone X e m r htc` →
   `regime_monotoneExt X e m r htc` (gives monotoneStepExt X.regime (ctxAfter X r).regime (fun k=>X.nextTag≤k)).
   Then fix the downstream backward uses with the discharge above.
3. Application-type-mismatch ×16 + Type-mismatch: Ext-arg / Post-arg propagation through the now-Ext
   forwarders (same threading already done in ExternBoundary).
4. BUG at 20467: `exact hClosFull _ hσcap₀_mem` — `hσcap₀_mem` is undefined; replace with the in-scope pfn
   closure membership (`hsource₀` is the static-source fact from the rcases at ~20059; the tcl∈tcls
   membership for `PFnTClosure.regular x₀ pbody₀ σcap₀` must be found/derived — check
   `applyPFnTClosure_regular_inv_of_threaded_mem` outputs).

DISCRIMINATING CHECK (advisor): verify `h_clean_res_to_pre` (~8358) with a real build / lean_goal — the 2nd
agent could NOT confirm whether it's a bounded backward-discharge or a genuine `ExternBoundarySpec.regimeFR`
(Phase D) need. Resolve before declaring App near-done. Do NOT trust the continuation doc's blanket
"no site needs regimeFR" (same unreliable pass produced it). Continuation detail also in
doc/extern-regime-stepFRApp-continuation.md (treat its verification claims as lean-lsp, i.e. suspect).

AFTER StepFRApp green: FaultRobustnessProofs (masked dispatch supplies the 2 new Post hyps —
hmasked_bounded := `fun k hk => absurd hk id`/`nomatch hk` since masked≡False at top, hbnd from StepFRPost
TagBoundedCtx), Progress/MemoryMonotonicity (rebuild-check, likely fine), then Phase D / Phase E.

## StepFRApp leaf-block conversion templates (consolidated)

(Merged from the now-deleted stepFRApp-continuation.md. CAVEAT: that doc's per-block
"GREEN"/error-count claims were lean-lsp-based and were CONTRADICTED by a real `lake build`
— ignore any status assertion; trust only `lake build LeanProofs.StepFRApp`. The TEMPLATES
below are sound; the STATUS isn't.)

CONVERTED SHARED LAYER (the load-bearing migration; reference, don't relitigate):
- Kernel member lemmas now take `(hmono_pre_to_src : monotoneStepExt preCtx.regime
  (ctxAfter ctx src).regime (fun k => preCtx.nextTag ≤ k))` + `(hbnd_pre : TagBoundedCtx preCtx)`
  instead of a full `∀ k b` backward lookup: `appMember_consistentWithRegime_from_body`,
  `consistentWithRegimeMasked_app_member_from_body`, and the `AppMemberCtxCons` def. Var conjunct
  → `varsRegime_monotoneExt` + `TagBoundedCtx_varEnv_guardTag_lt`; captured conjunct →
  `closureCapturedVarsRegime[Masked]_monotoneExt` + `TagBoundedCtx_varEnv_etypClosures`;
  `hnewB := (fun _ hk => hk)` (B = preCtx.nextTag).
- Forwarders (`appTwoRunOutPack_*`, `appSingleRunMaskedPost_*`, `appTwoRunOutChoice_*`, the two
  `src₀/src₁` two-run extern member lemmas) thread `hmono_pre_to_src(/₀/₁)` + `hbnd_pre`.
- `applyFn/PFnTClosure_staticSource_of_threaded_mem` OUTPUT `monotoneStepExt bodyState.regime'
  first.regime' (fun k => bodyState.nextTag' ≤ k)` (proof weakens the cursor-floor Ext via
  `monotoneStepExt_weaken` + `htag : bodyState.nextTag' ≤ cursor.1`).
- `applyFn/PFnTClosure_staticSource_clean_back_of_p1p_true` (producer def ~6304) now takes, after
  `hp1p`: `hlookupBack` (Ext mono) `hmemGuardBnd` (∀ l qt k, bodyState.memEnv'.lookup l=some qt →
  qtypGuardTag qt=some k → k<bodyState.nextTag') `hbodyCtx_mem` `hbodyCtx_regime` `hbodyCtx_pc`
  `hbnd_body : TagBoundedCtx bodyCtx` `hwfBody`; guard-case backward via `monotoneStepExt_lookup_back`.
- Reusable helper `tagBoundedCtx_closure_body` (def ~2179): produces `TagBoundedCtx bodyCtx` from
  `(hCapBoundBase : CapturedEnvFullBounded σcap result1.nextTag')` + `hbnd` (TagBoundedCtx ctxᵢ) +
  `hbnd1` (TagBoundedCtx (ctxAfter (ctxAfter ctxᵢ result2) result1)) + `hcursorTag`. Takes
  `(pcBody : Poison) (pureCtxBody : Bool)`: fn callers `pureCtxBody := ctxᵢ.pureCtx`,
  pfn callers `pureCtxBody := true`; pcBody must match the bodyCtx literal's `pc` exactly
  (fn extern body: `joinPoison p (joinPoison p1 ctxᵢ.pc)`). bodyCtxE₀ (~15158) is exactly this shape.

LEAF-BLOCK TEMPLATES (replay per fn/pfn × U/E × ₀/₁ block; the blocks are symmetric):
1. `regime_monotone bodyCtx* … htcBody*'` (DELETED) → `regime_monotoneExt …` giving
   `monotoneStepExt bodyCtx*.regime (ctxAfter bodyCtx* result3*).regime (fun k=>bodyCtx*.nextTag≤k)`,
   then `monotoneStepExt_weaken … (fun k hk => Nat.le_trans (by simpa [bodyCtx*] using hcursorTag*) hk)`
   + `simpa [bodyCtx*, ctxAfter, hfirst*_eq]` to land floor `result1.nextTag'`. Drop the old
   `regime_lookup_back_of_monotone`; pass the Ext mono + `hbnd1`/`_htagBounded1` to the consumer.
2. `typecheckExpr_lookup_clean_back_of_pc_true … hwfBody* hpc_body*` → insert the body's
   `TagBoundedCtx` (`htagBoundedBody*` via tagBoundedCtx_closure_body) BEFORE `hpc_body*`; fix the
   sibling `… hwf2 hpc2` site to insert `hbnd2`. (`introN failed` / `… of sort Prop` are cascades
   that clear once the arg count is right.)
3. `applyFn/PFnClosuresThreaded_join_regime_mono` ALREADY returns `monotoneStepExt result1.regime'
   res.regime' (fun k=>result1.nextTag'≤k)` — so at its call sites just retype the enclosing
   `have h_mono_res/hpre_to_res_mono : Regime.monotoneStep …` to the Ext form (hpre_to_res floor
   `(ctxAfter (ctxAfter ctxᵢ result2) result1).nextTag`). Where a leaf hand-rolls
   `h_all_members_mono` + `joinTypeResults_regime_monotone`, replace the block with one
   `applyFn/PFnClosuresThreaded_join_regime_mono …` call. Downstream `cleanUnder_of_monotone` /
   `agreeValueUnder_clean_monotoneRegime` → `_ext` with `(fun _ hk => hk)` + per-qt bound
   (`qtypPredTagBounded qt B` via `TagBoundedCtx_varEnv_predTagBounded`; `etypClosuresFullBounded
   qt.etyp B` via `TagBoundedCtx_varEnv_etypClosures`; B = result1.nextTag').
   (`agreeValueUnder_clean_monotoneRegime_ext` lives in JoinMemberTransport.lean, green.)
4. `hlookupBack* k b …` applied as a function ("Function expected") → for a standalone `∀ k b`
   rebuild use `simpa using hlookupBack*` to land the Ext mono; for a guard-tag use,
   `TagBoundedCtx_memEnv_guardTag_lt … + monotoneStepExt_lookup_back`.
5. masked `.2` "expected ∀ k, masked k → k < nextTag" → insert `hmasked_bounded_body
   htagBoundedBody` between `hmasked_absent_body` and `hcwr_body`.
6. Leaf calls passing `hlookup_back_res1_to_*` → pass the Ext mono (`hres1_to_*_mono`/`hmono_res1_to_*`/
   `hlookupBack*` massaged) and, for `appMember`, also `hbnd1`/`_htagBounded1`.
7. CONSUMER ARG-SHIFT (the `simp made no progress` family, e.g. ~15618): the
   staticSource_clean_back CALL sites still pass the OLD 5-arg tail; they need `hmemGuardBnd`
   (from `_htagBounded1` via `TagBoundedCtx_memEnv_guardTag_lt`, over result1.memEnv'=bodyCtx.memEnv)
   inserted after `hlookupBack`, and `hbnd_body : TagBoundedCtx bodyCtx` (via tagBoundedCtx_closure_body)
   inserted before `hwfBody`.
KNOWN BUG (~line 20467, pfn-U₀): `exact hClosFull _ hσcap₀_mem` references an undefined identifier;
replace with the in-scope pfn closure membership (`hsource₀`/derived `… ∈ tcls`).

GENUINELY CAREFUL SUB-PART: the p1=true two-run `agreeOnClean` `¬qtypCleanUnder` conjunct (Shared/U/E
blocks, around `h_all_members_mono`/`joinTypeResults_regime_monotone`/`h_clean_res_to_pre` and the
`agreeOnClean_closure_body_start`/`agreeValueUnder_clean_monotoneRegime_ext` machinery) does backward
clean transport res→result1. Bound each member qt's guard tag from the member/join TagBoundedCtx —
spend review attention here. ESCALATE to `ExternBoundarySpec.regimeFR` (Phase D) ONLY if a member qt's
guard tag is provably NOT bounded by result1.nextTag' (advisor's open flag on `h_clean_res_to_pre`
~8358; not observed yet — confirm with a real build / lean_goal before declaring App near-done).
