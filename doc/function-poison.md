# Function Poison: Design Specification

This document specifies the semantics of function poison in Poison and the
corresponding proof obligations for fault-robustness. The design resolves the
`stepFR_app` proof obstacle by gating closure agreement on the arrow's internal
poison.

## Background: Two Poison Carriers for Functions

Function values carry poison information in two places:

- **Outer poison (qualified type)**: the `p` in `QTyp` / `Q` (`T :> p {P}`).
  Generic poison flag for expression results.

- **Internal poison (arrow type)**: the `p` in arrow/parrow types
  (`ST1 -> ST2 # p …`). Function-specific poison that records the `pc` at the
  function's definition site.

### Semantic Distinction

- **Definition-time control taint** (internal `# p`): Records the program-counter
  poison at the function's definition site. Stored in the type because the body
  is re-typechecked at application time.

- **Call-site provenance taint** (outer `Q.poison`): Tracks reliability of the
  function value as an expression result (e.g., selection under poisoned control
  flow).

## Design Decision: Internal Poison Governs Closure Agreement

**Chosen approach**: Gate closure agreement predicates on the *internal* arrow
poison, not on outer `Q.poison`.

### Rationale

The fault-robustness step theorem requires `agreeOnClean` for the body's typing
context when proving the `app` case. This requires agreement of captured runtime
environments on clean entries. For "dirty functions" (where internal poison is
not clean), the proof cannot establish this premise—nor should it need to,
because dirty functions produce dirty results regardless.

### Key Principle

- **If internal poison is clean**: Closure agreement requires same body and
  agreement of captured environments on entries that are clean-under-R.
- **If internal poison is dirty**: No closure agreement constraints. Different
  bodies and captured environments are permitted across runs. Application results
  are not required to agree.

## Design Decision: No De-poisoning for Functions

**Chosen approach**: Functions cannot be de-poisoned via guard tags.

### Definition

```
internalPoisonClean(qt) :=
  match qt.etyp with
  | arrow _ _ p _  => p = false
  | parrow _ _ p _ => p = false
  | _              => True
```

Internal poison is clean-under-R if and only if the internal poison boolean is
literally `false`. Guard tags on `QTyp.pred` do **not** de-poison the internal
arrow poison.

### Rationale

1. **Semantic clarity**: Internal poison reflects definition-time `pc`. Guard
   tags verify properties of values, not definition contexts. Conflating these
   is semantically unsound.

2. **Proof simplicity**: Avoids additional case analysis for guard-based
   de-poisoning in closure agreement proofs.

3. **Practical impact**: Functions rarely carry guard tags in typical code
   patterns. The expressiveness loss is minimal.

4. **Future extensibility**: If guard-based de-poisoning is later needed, the
   design can be extended by modifying `internalPoisonClean` without
   restructuring the proof architecture.

## Lean Implementation

### New Predicate: `internalPoisonClean`

```lean
def getInternalPoison (et : ETyp) : Option Poison :=
  match et with
  | ETyp.arrow _ _ p _ => some p
  | ETyp.parrow _ _ p _ => some p
  | _ => none

def internalPoisonClean (qt : QTyp) : Prop :=
  match getInternalPoison qt.etyp with
  | none => True        -- non-function types
  | some p => p = false -- clean iff internal poison is literally false
```

### Modified `agreeValueUnder` for Closures

Add cases that gate on internal poison:

```lean
-- Clean internal poison: require same body + captured env agreement
| clean_internal_arrow {qt : QTyp} {tcl : FnTClosure} ...
    (hclean : internalPoisonClean qt)
    (hetyp : qt.etyp = ETyp.arrow st1 st2 p tcls)
    (htcl : tcl ∈ tcls)
    (hmatch : tcl = FnTClosure.regular x body σcap)
    (hcap : agreeCapturedEnv predSat R μ₁ μ₂ θ₁ θ₂ σcap ρcap₁ ρcap₂)
    (hv₁ : v₁ = Value.closure x body ρcap₁)
    (hv₂ : v₂ = Value.closure x body ρcap₂) :
    agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂

-- Dirty internal poison: no constraints
| dirty_internal_arrow {qt : QTyp} {v₁ v₂ : Value}
    (hdirty : ¬ internalPoisonClean qt)
    (hisArrow : qt.etyp.isArrow = true) :
    agreeValueUnder predSat R μ₁ μ₂ θ₁ θ₂ qt v₁ v₂

-- Similarly for parrow...
```

### Impact on Existing Proofs

| Lemma | Change Required |
|-------|-----------------|
| `stepFR_fn` | Use `clean_internal_arrow` when `ctx.pc = false`; otherwise `dirty_internal_arrow` |
| `stepFR_pfn` | Same pattern as `stepFR_fn` |
| `stepFR_app` | Check internal poison; only establish `agreeCapturedEnv` when clean |
| `agreeCapturedEnv_of_agreeOnClean` | No change; called conditionally |
| `agreeValueUnder_transport_clean` | Update to handle new closure cases |

### `stepFR_app` Proof Strategy

1. Extract internal poison `p` from the function's arrow type
2. **Case `p = false`** (clean internal):
   - Establish `agreeCapturedEnv` using `agreeCapturedEnv_of_agreeOnClean`
   - Apply IH for body with `agreeOnClean` premise
   - Conclude result agreement via `clean_internal_arrow`
3. **Case `p = true`** (dirty internal):
   - Use `dirty_internal_arrow` for function agreement (no constraints)
   - Result agreement not required (dirty function → dirty result)
   - No need to establish `agreeCapturedEnv`

## Summary

| Aspect | Decision |
|--------|----------|
| Agreement gate | Internal arrow poison, not outer `Q.poison` |
| De-poisoning | Not supported for functions |
| Clean internal | Same body + `agreeCapturedEnv` on clean entries |
| Dirty internal | No constraints; any closures "agree" vacuously |
