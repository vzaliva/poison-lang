## Current status of the proof

The proof of the "main" theorem (typechecker implies noninterference)
is divided in two parts:

### The "step" theorem

`TypeSystemEnforcesNonInterference_step`: the proof that if
typechecker satisfies "step" specification it must also satisfy "main"
specification. The "step" specification is designed to be easily
provable by induction and to support multi-step reasoning (when the
output if the typechecker becomes an input of another call of the
typechecker). This theorem is not proved yet.

### The "bridge" lemna

`TypeSystemEnforcesNonInterference_impl`: the proof that "step"
specification implies "main" specification. This lemma depends on the
property that typechecker satisfies "guardless if clean" invariant.
The invariant says that if the typechcekcer's input satisfies
"guardless if clean" property, so does the output.

During the proof of "guardless if clean" invariant it was observed
that it needs to be formulated in a "deep" way in order to be provable
by induction. The property is called "deep" when it is applied not
only to the QType or the list of QTypes, but also to the QTypes in
captured environment if QType is a closure. `deepVarEnvProperty`
provides a general construction to make a property "deep".

The "guardless if clean" invariant is proved and the lemma is almost
proved - right now the proof relies on two lemmas with incomplete
proofs.

`wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanMem` and
`wfInputSpec_and_ctxMatchecInputSpec_imply_guardlessIfCleanVars`: this
lemmas establish the fact that if the assumptions of the "main"
specification hold, then typechecker inputs satisfy the "guardless if
clean" property. These lemmas are needed to apply the "guardless if
clean" invariant.

I have a conjecture that in order to complete the proof of these
lemmas some properties involved in the "main" and "step"
specifications (i.e. `wfInputSpec`, `ctxMatchesInputSpec`) must also
be made "deep".

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

3. **`NonInterferenceProofs.lean`**
   - Statement: `NonInterference.lean`
   - Status: All proof code commented out with `/- TODO: this proof needs repairs. -/`
   - Notes: Proof structure is present but needs completion

4. **`TypecheckPExprPreservesTypestateProofs.lean`**
   - Statement: `TypecheckPExprPreservesTypestate.lean`
   - Status: All proof code commented out with `/- TODO: this proof needs repairs. -/`
   - Notes: Proof structure is present but needs completion

5. **`GuardlessIfClean.lean`**
   - Status: Entire file marked with `/- TODO: this proof needs repairs. -/` at the top
   - Notes: This file contains both definitions and proofs. The proofs need to be updated
     to handle merged typing closures (lists of closures instead of single closures).
     Recent changes to support merged closures have been made but proofs need repair.

### Files with active proofs

The following files contain active proofs that compile:

- `Equality.lean` - Proofs for BEq, LawfulBEq, and DecidableEq instances
- `JoinMemEnv.lean` - Proofs for memory environment joining operations
- `LookupUpdate.lean` - Proofs for lookup and update operations
- `MemoryMonotonicity.lean` - Proofs for memory monotonicity properties
- `Properties.lean` - Various type safety properties
- `TypeSafety.lean` - Type safety lemmas
- `ToExpr.lean` - Proofs related to expression conversion
- `VarEnvPreservation.lean` - Proofs for variable environment preservation
- `IOHelpers.lean` - Helper functions for IO-related proofs

### Recent changes affecting proofs

The implementation of merged typing closures (Issue #63) changed arrow types from
carrying a single closure to carrying a list of closures (`List FnTClosure` and
`List PFnTClosure`). This change required updates to:

- `Equality.lean` - Updated to handle list equality for closures
- `JoinMemEnv.lean` - Updated to use `joinPredicates` function
- `GuardlessIfClean.lean` - Updated inductive definitions to handle lists (needs repair)
- `NonInterference.lean` - Updated `deepQTypProperty` to check all closures in lists
