## Current status of the proof

The proof of the "main" theorem (typechecker implies noninterference)
is divided in two parts:

### The "step" theorem

`TypeSystemEnforcesNonInterference_step`: the proof that if
typechecker satisfies "step" specification it must also satisfy "main"
specification. The "step" specification is designed to be easily
provable by induction and to support multi-step reasoning (when the
output of the typechecker becomes an input of another call of the
typechecker). This theorem is not proved yet.

### The "bridge" lemma

`TypeSystemEnforcesNonInterference_impl`: the proof that "step"
specification implies "main" specification. This lemma depends on the
current agreement relation for values. The proof no longer relies on
the "guardless if clean" invariant. Instead, the non-interference
definition was strengthened so that clean values must agree by equality
(and clean references must agree via locset-based realization), and
poisoned values with no predicate can also agree by equality. This
removes the need to prove "clean implies no predicate" to discharge
agreement cases.

## Proof files status

### Files with proofs commented out (need repair)

The following proof files have been split into statement and proofs
files, with the proofs commented out and marked as needing repair:

1. **`ProgressProofs.lean`**
   - Statement: `Progress.lean`
   - Status: All proof code commented out with `/- TODO: this proof needs repairs. -/`
   - Notes: Proof structure is present but needs completion

2. **`PreservationProofs.lean`**
   - Statement: `Preservation.lean`
   - Status: All proof code commented out with `/- TODO: this proof needs repairs. -/`
   - Notes: Proof structure is present but needs completion

### Files with proofs in progress

1. **`NonInterferenceProofs.lean`**
   - Statement: `NonInterference.lean`
   - Status: Proofs are active but contain `sorry` placeholders
   - Notes: The bridge proof now uses the strengthened agreement relation

### Removed files

- `GuardlessIfClean.lean` - Removed (guardless reasoning is no longer used in the NI bridge proof)

### Files with completed proofs

The following files contain completed proofs that compile:

- `Equality.lean` - Proofs for BEq, LawfulBEq, and DecidableEq instances
- `JoinMemEnv.lean` - Proofs for memory environment joining operations
- `LookupUpdate.lean` - Proofs for lookup and update operations
- `MemoryMonotonicity.lean` - Proofs for memory monotonicity properties
- `Properties.lean` - Various type safety properties
- `TypeSafety.lean` - Type safety lemmas
- `ToExpr.lean` - Proofs related to expression conversion
- `VarEnvPreservation.lean` - Proofs for variable environment preservation
- `IOHelpers.lean` - Helper functions for IO-related proofs
- `TypecheckPExprPreservesTypestateProofs.lean` - Proofs are complete; some linter options are disabled in-file

### Recent changes affecting proofs

The implementation of merged typing closures (Issue #63) changed arrow types from
carrying a single closure to carrying a list of closures (`List FnTClosure` and
`List PFnTClosure`). This change required updates to:

- `Equality.lean` - Updated to handle list equality for closures
- `JoinMemEnv.lean` - Updated to use `joinPredicates` function
- `NonInterference.lean` - Updated `deepQTypProperty` to check all closures in lists
- `NonInterference.lean` - `agreeValueUnder` strengthened to enforce agreement
  for clean values and for poisoned values without predicates
