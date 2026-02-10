## Issue #101 Proposal (Final): Fixed-Parameter Deep Tag-Meaning Invariant

Original issue: https://github.com/vzaliva/poison-lang/issues/101

---

## 1. Constraints

These constraints drive the design and rule out heavier alternatives.

1. **Use-site information is often tag-only**
   - `matchGuard` returns only `(k, deps)` (`LeanPoison/Typecheck.lean`).
   - Many FR judgments consume only `qtypGuardTag` / regime lookup, i.e. tag-level
     information.
   - `guardOnly k` carries no closure descriptor; yet FR still reasons with `k`.
   - Therefore `PredSat` must remain usable when only `k` is available.

2. **Non-executable invariants should be inductive**
   - For proof-oriented membership/consistency properties, inductive definitions
     are preferred over executable booleans or large folded predicates.
   - Inductive forms support inversion and local proof steps directly.

3. **Minimize proof churn**
   - This is a tradeoff, not an absolute. In raw edit count, threading one more
     invariant through `StepFR` may touch more lemmas than changing a single
     signature.
   - However, changing `PredSat` arity tends to force deeper semantic rewrites
     at tag-only use sites (`guardOnly`, regime checks, `matchGuard` consumers).
   - We still prefer keeping `PredSat := Tag → Memory → Value → Prop` because
     many core judgments are tag-only and include `guardOnly` cases with no
     descriptor payload.
   - Net expectation: fixed-`tm` propagation is broader but mostly mechanical;
     descriptor-indexed `PredSat` is narrower in signatures but deeper in logic.

4. **Fix the contradiction structurally, not by proof-script discipline**
   - #101 arises from unconstrained re-instantiation of `match_iff` across
     contexts.
   - The law must therefore fix one `tm` parameter for the whole derivation path
     (not quantify `tm` inside `match_iff`).

5. **Keep extern/function-application compatibility in view**
   - Any context invariant introduced at `StepFR` level must be preservable across
     context-transforming branches (notably extern insertions).

6. **Handle fresh-tag introduction**
   - Tags introduced by typing (`frand`, extern-related insertions) must still be
     interpreted by the same fixed `tm`.
   - So top-level assumptions must provide a `tm` that covers every descriptor
     that can appear in contexts along the proof derivation.

---

## 2. Problem Restatement

`PredSatLaws.match_iff` currently quantifies over arbitrary typing environments
`σ : VarTypeEnv` and `Γ : MemoryTypeEnv`, but concludes about
`predSat k μ v` indexed only by tag `k`.

This enables the #101 contradiction:

- instantiate `match_iff` with context where `k ↦ D_true`,
- instantiate again with context where `k ↦ D_false`,
- derive both `predSat k μ v` and `¬ predSat k μ v`.

Each context may be internally unique, yet the same tag has different global
meaning across instantiations.

Success criterion for this proposal: within one FR proof derivation, it must be
impossible to derive both `predSat k μ v` and `¬ predSat k μ v` by instantiating
`match_iff` with incompatible context meanings for the same tag.

---

## 3. Proposal 1 (Minimal-Churn, Fixed-Parameter `TagMeaning`)

### 3.1 Keep `PredSat` unchanged

```lean
abbrev PredSat := Tag → Memory → Value → Prop
```

Rationale: at key use-sites we only have tag-level information (`k`, `deps`,
regime lookup). A descriptor-indexed `PredSat` remains a fallback, but not the
primary plan.

### 3.2 Add `TagMeaning` and deep inductive context membership

```lean
structure GuardDesc where
  argName : Name
  body    : PExpr
  capEnv  : CapturedVarEnv
deriving Repr, BEq
```

```lean
abbrev TagMeaning := ExtTreeMap Tag GuardDesc

namespace TagMeaning
  @[inline] def lookup (tm : TagMeaning) (k : Tag) : Option GuardDesc :=
    tm.get? k

  @[inline] def update (tm : TagMeaning) (k : Tag) (d : GuardDesc) : TagMeaning :=
    tm.insert k d

  /-- `tm` contains a binding for `k`. -/
  def hasKey (tm : TagMeaning) (k : Tag) : Prop :=
    tm.contains k
end TagMeaning
```

Optional note: `BEq`/`Repr` instances can be added (as with other env wrappers)
for debugging/printing convenience.

```lean
def qtypGuardDesc? (qt : QTyp) : Option (Tag × GuardDesc) :=
  match qt.pred with
  | Predicate.guardClosure k arg body cap =>
      some (k, { argName := arg, body := body, capEnv := cap })
  | _ => none
```

```lean
/-- Extract captured typing env from closures. -/
def fnCapturedEnv : FnTClosure → CapturedVarEnv
  | .regular _ _ ρ => ρ
  | .extern _ _ _ ρ => ρ

def pfnCapturedEnv : PFnTClosure → CapturedVarEnv
  | .regular _ _ ρ => ρ
  | .extern _ _ ρ => ρ
```

```lean
/-- Deep occurrence of a QTyp inside another QTyp. -/
inductive QTypInQTyp : QTyp → QTyp → Prop where
  | self (qt : QTyp) :
      QTypInQTyp qt qt
  | in_arrow (qtInner qtOuter : QTyp)
      (st₁ st₂ : Typ) (p : Poison) (tcls : List FnTClosure)
      (tcl : FnTClosure) (x : Name) :
      qtOuter.etyp = ETyp.arrow st₁ st₂ p tcls →
      tcl ∈ tcls →
      (x, qtInner) ∈ fnCapturedEnv tcl →
      QTypInQTyp qtInner qtOuter
  | in_parrow (qtInner qtOuter : QTyp)
      (st₁ st₂ : Typ) (p : Poison) (tcls : List PFnTClosure)
      (tcl : PFnTClosure) (x : Name) :
      qtOuter.etyp = ETyp.parrow st₁ st₂ p tcls →
      tcl ∈ tcls →
      (x, qtInner) ∈ pfnCapturedEnv tcl →
      QTypInQTyp qtInner qtOuter
  | trans (qt₁ qt₂ qt₃ : QTyp) :
      QTypInQTyp qt₁ qt₂ →
      QTypInQTyp qt₂ qt₃ →
      QTypInQTyp qt₁ qt₃
```

```lean
/-- Deep occurrence of a QTyp in (σ, Γ): start from top-level entries, then descend
    through closure-captured environments using `QTypInQTyp`. -/
inductive QTypInEnvs : QTyp → VarTypeEnv → MemoryTypeEnv → Prop where
  | inVar (σ : VarTypeEnv) (Γ : MemoryTypeEnv)
      (x : Name) (qt qtRoot : QTyp) :
      σ.lookup x = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInEnvs qt σ Γ
  | inMem (σ : VarTypeEnv) (Γ : MemoryTypeEnv)
      (l : Loc) (qt qtRoot : QTyp) :
      Γ.lookup l = some qtRoot →
      QTypInQTyp qt qtRoot →
      QTypInEnvs qt σ Γ
```

```lean
/-- Deep membership of guard descriptors reachable from (σ, Γ). -/
inductive GuardDescInEnvsDeep (σ : VarTypeEnv) (Γ : MemoryTypeEnv) : Tag → GuardDesc → Prop where
  | intro (qt : QTyp) (k : Tag) (d : GuardDesc) :
      QTypInEnvs qt σ Γ →
      qtypGuardDesc? qt = some (k, d) →
      GuardDescInEnvsDeep σ Γ k d
```

```lean
inductive EnvRespectsTagMeaning (tm : TagMeaning) (σ : VarTypeEnv) (Γ : MemoryTypeEnv) : Prop where
| intro :
    (∀ {k d}, GuardDescInEnvsDeep σ Γ k d → tm.lookup k = some d) →
    EnvRespectsTagMeaning tm σ Γ
```

### 3.3 Critical fix: make `tm` a structure parameter of `PredSatLaws`

```lean
structure PredSatLaws (predSat : PredSat) (tm : TagMeaning) : Prop where
  match_iff :
    ∀ (mode : LeanPoison.EvalMode) (condition : Expr)
      (Γ : MemoryTypeEnv) (σ : VarTypeEnv)
      (k : Tag) (deps : Deps)
      (μ : Memory) (ρ : VarEnv) (θ : RealizationMap)
      (addr : Address) (pm : Bool) (cfg : Config)
      (v : Value) (b : Bool),
      EnvRespectsTagMeaning tm σ Γ →
      matchGuard condition Γ σ = .ok (k, deps) →
      terminatesTo mode condition
        { memory := μ, varEnv := ρ, nextAddr := addr, pureMode := pm } cfg
        (Value.bool b) →
      ((∃ (x : Name) (qt : QTyp),
          σ.lookup x = some qt ∧ qtypGuardTag qt = some k ∧ ρ.lookup x = some v)
        ∨
       (∃ (x : Name) (qt memQt : QTyp) (t : ETyp) (ls : LocSet)
          (l0 : Loc) (a : Address) (n : Int),
          σ.lookup x = some qt ∧
          qt.etyp = ETyp.ref t ls ∧
          l0 ∈ ls ∧ Γ.lookup l0 = some memQt ∧ qtypGuardTag memQt = some k ∧
          θ.lookup l0 = some a ∧ μ.lookup a = some n ∧ v = Value.num n)) →
      (b = true ↔ predSat k μ v)

  mem_monotone : ...
```

Why this matters: once `h_laws : PredSatLaws predSat tm` is fixed in a theorem,
`match_iff` cannot be re-instantiated with a different `tm₂`. The type enforces
one shared tag meaning for the entire derivation.

### 3.4 Use the same fixed `tm` in `StepFR` and top-level FR theorem

```lean
def wfTagMeaningCtx (tm : TagMeaning) (ctx : TypeContext) : Prop :=
  EnvRespectsTagMeaning tm ctx.varEnv ctx.memEnv
```

`StepFR` shape change:

```lean
def StepFR ... (predSat : PredSat) (tm : TagMeaning) : Prop :=
  ∀ (h_laws : PredSatLaws predSat tm),
    ...
    wfTagMeaningCtx tm ctx →
    ...
    ∃ θ₀' θ₁',
      ...
      wfTagMeaningCtx tm (ctxAfter ctx res) ∧
      ...
```

Top-level FR shape change (regular + IO-free mirror):

```lean
∀ (predSat : PredSat) (tm : TagMeaning) (h_laws : PredSatLaws predSat tm),
  wfTagMeaningCtx tm ctx →
  ...
```

Proof-engineering note: for tag-introducing steps, `wfTagMeaningCtx tm (ctxAfter ctx res)`
does not follow from `wfTagMeaningCtx tm ctx` alone. The branch proof must show
that each newly introduced `(k, d)` also satisfies `tm.lookup k = some d`.
Under this design, that obligation is discharged by the caller's top-level choice
of fixed `tm` (covering all tags reachable in the derivation), not by changing
`tm` during `StepFR`.

### 3.5 Satisfiability witness (informal)

`PredSatLaws predSat tm` is not vacuous. A canonical model is:

```lean
def predSatFrom (tm : TagMeaning) : PredSat :=
  fun k μ v =>
    ∃ d, tm.lookup k = some d ∧ evalGuardDesc d μ v = true
```

Here `evalGuardDesc` is a placeholder for the existing guard-body evaluation
relation/function. With the corresponding guard-evaluation correctness lemmas,
`match_iff` is provable for `predSatFrom tm` under
`EnvRespectsTagMeaning tm σ Γ`.

---

## 4. Use-Site Adequacy (Why `PredSat` stays tag-indexed)

This proposal intentionally does **not** enrich `PredSat` with descriptor data.
Reason: major use-sites often know only `k` or `matchGuard` output.

1. `matchGuard` output is `(k, deps)` only.
2. `consistentWithRegime` and `valueConsistentWithRegime` are tag/regime driven.
3. `guardOnly k` carries no descriptor but still participates in FR reasoning.

So the right split is:

- keep `PredSat` tag-indexed,
- enforce descriptor consistency separately via fixed `tm`, with
  `EnvRespectsTagMeaning tm ...`.

### Fresh-tag behavior (`frand` / extern insertion)

Note: in the current implementation, `frand` introduces fresh guard tags;
`rand` itself is typed with `noPred` and does not introduce tags.

Under Option 1 (fixed `tm`), we do **not** change the map during the proof.

- Top-level theorem takes one `tm` and one `h_laws : PredSatLaws predSat tm`.
- That `tm` must already cover descriptors for every tag that can appear in
  contexts along the derivation.
- Per-step obligation is only:
  `wfTagMeaningCtx tm (ctxAfter ctx res)`.
- Tag-introducing branches (`frand`, extern insertions) require local lemmas:
  if `ctxAfter` inserts `(k, d)`, then `tm.lookup k = some d`.
- In the IO-free fragment, tags are program-determined (no runtime random tag
  allocation), so constructing such a global `tm` is straightforward.

This removes any need to transport `PredSatLaws` from `tm` to `tm'`.

### Clarification: "one static context" in `StepFR`

`StepFR` compares **two runs** that share the same typing context `ctx`:

- run 0 starts from `(μ₀, ρ₀, θ₀, a₀)`,
- run 1 starts from `(μ₁, ρ₁, θ₁, a₁)`.

So there are two memories/two var-envs/two realization maps, but one static
typing context used for both premises:

- `runtimeInstantiatesCtx ctx μ₀ ρ₀ θ₀`
- `runtimeInstantiatesCtx ctx μ₁ ρ₁ θ₁`

and one shared post-typing context in the conclusion:

- `ctxAfter ctx res`

for both final runs.

---

## 5. How This Exactly Solves #101

Let:

- `D_true  = ⟨"a", PExpr.bool true,  []⟩`
- `D_false = ⟨"a", PExpr.bool false, []⟩`

Assume one FR theorem instance with fixed
`h_laws : PredSatLaws predSat tm`.

Suppose #101 attempts two `match_iff` instantiations in that same proof:

1. with `σTrue` containing a closure descriptor `(k, D_true)`,
2. with `σFalse` containing a closure descriptor `(k, D_false)`.

From `EnvRespectsTagMeaning tm σTrue ΓTrue`, by inversion:
- `GuardDescInEnvsDeep σTrue ΓTrue k D_true`
- therefore `tm.lookup k = some D_true`.

From `EnvRespectsTagMeaning tm σFalse ΓFalse`, similarly:
- `tm.lookup k = some D_false`.

Hence `some D_true = some D_false`, so `D_true = D_false`, contradiction.

Therefore both contradictory instantiations cannot coexist under one shared `tm`.
This is exactly what failed before: the old formulation allowed switching to a
different `tm₂` on a second `match_iff` use. The new type
`PredSatLaws predSat tm` prevents that by construction.

Scope note: the fix criterion is that the FR theorem path can no longer derive
both `predSat k μ v` and `¬ predSat k μ v` by switching typing contexts while
keeping one theorem-local `h_laws : PredSatLaws predSat tm`.

---

## 6. Proof Impact Analysis

### 6.1 Expected edits

`LeanProofs/FaultRobustness.lean`
- add `GuardDesc`, `qtypGuardDesc?`,
  `TagMeaning`, `QTypInQTyp`, `QTypInEnvs`, `GuardDescInEnvsDeep`,
  `EnvRespectsTagMeaning`, `wfTagMeaningCtx`;
- change `PredSatLaws` to `PredSatLaws (predSat) (tm)` and keep
  `EnvRespectsTagMeaning tm ...` in `match_iff`.

`LeanProofs/FaultRobustnessProofs.lean`
- add fixed `tm` parameter to `StepFR`/`StepFR_IH` and derived theorems;
- keep one shared `h_laws : PredSatLaws predSat tm` through the whole chain;
- pass the new precondition at `match_iff` use sites.

Top-level FR specs
- add `tm` parameter and `wfTagMeaningCtx tm ctx` premise in regular and
  IO-free signatures.

### 6.2 Why this is lower impact than alternatives

1. `PredSat` arity unchanged (largest churn source avoided).
2. Agreement relations (`agreeValueUnder`, etc.) remain structurally intact.
3. No `PredSatLaws` chaining across map extensions is needed.
4. Most edits are signature propagation + local context-preservation lemmas;
   deep invariants still require nontrivial inversion/transport lemmas.

### 6.3 New proof obligations

1. Initial-context premise: `wfTagMeaningCtx tm ctx`.
2. Per-step preservation:
   `wfTagMeaningCtx tm (ctxAfter ctx res)`.
3. Tag-introducing branch lemmas (`frand`/extern insertion):
   any inserted `(k, d)` in `ctxAfter` must satisfy `tm.lookup k = some d`.
4. Deep-invariant lemmas for closure restoration/application paths:
   preserving `QTypInEnvs`/`GuardDescInEnvsDeep` under context updates.

---

## 7. Migration Plan

1. Add `TagMeaning` + deep inductive definitions
   (`QTypInQTyp`, `QTypInEnvs`, `GuardDescInEnvsDeep`).
2. Change `PredSatLaws` to take fixed `tm` as a structure parameter.
3. Update `StepFR`, `StepFR_IH`, and top-level FR statements to use one fixed
   `tm` and one shared `h_laws : PredSatLaws predSat tm`.
4. Repair all `match_iff` call sites; they now use theorem-fixed `tm`
   structurally (no ad-hoc map instantiation argument).
5. Add/update preservation lemmas proving
   `wfTagMeaningCtx tm (ctxAfter ctx res)` for each step form.
6. For tag-introducing steps, add the local lookup lemmas connecting inserted
   descriptors to the fixed `tm`.

---

## 8. Discarded Material

Intentionally excluded from this revision to keep proof impact low:

- global pairwise deep-uniqueness frameworks (`EnvsPairwise`/`TagCompatible`) as
  the primary mechanism (we use deep membership + fixed `TagMeaning` instead),
- redesign of `PredSat` to descriptor-indexed form.

Those remain fallback options only if Proposal 1 proves insufficient.
