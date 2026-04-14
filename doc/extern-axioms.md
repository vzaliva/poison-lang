# Extern Functions: FR Contract Surface on `new-iofree`

## 1. Motivation

Extern forms (`externVal`, `externFn`, `externPfn`) are a placeholder for a
future FFI. Operationally, their runtime evaluation currently fails — this
is **temporary**: the runtime will be extended to dispatch externs once the
FFI is implemented. Until then, externs are operationally unreachable.

Even with the FFI unimplemented, externs still need to **typecheck soundly**
— and not only for future-proofing. The fault-robustness (FR) theorem reasons
about programs with conditionals whose guards can sometimes be determined
statically. When the FR proof walks such a conditional, the body of the
not-taken branch does not execute but must still typecheck. If that branch
contains an extern call, the typing rules for externs are on the critical
path of the proof even though no FFI machinery runs.

Externs therefore affect the FR proof only at the **typechecking summary**
layer, not at runtime.  The proof surface is about what the typechecker
states about external code.  Two obligations arise:

1. **Typechecking-to-semantics coherence for fresh guards.**
   Extern typechecking resolves symbolic predicates using
   `collectAndAllocExternTags` and `resolveSyntaxPred`.  The resulting
   predicates may mention freshly allocated tags, so the proof needs a
   contract connecting those fresh tags to an arbitrary `TagMeaning`.
2. **Typechecking-to-semantics coherence for impure memory effects.**
   An impure extern summary may overwrite memory cells with resolved guard
   predicates. The FR proof needs a contract saying that trusted output
   cells do not manufacture trust out of nowhere.

Neither obligation is derivable from the syntactic shape of the typechecker
alone, so each is discharged by one axiom. 

## 2. Contracts

### 2.1 Contract A: Tag Meaning Soundness

A `TagMeaning` is a finite map that interprets each allocated guard tag as
the closure it stands for — an argument name, a body, and a captured
environment.  A qualified type `qt` **respects** a tag meaning `tm`
(`QTypRespectsTagMeaning tm qt`) when every guard tag appearing anywhere
inside `qt` is mapped by `tm` to the closure that tag was allocated to
name.

When extern typechecking allocates fresh tags and resolves symbolic
predicates, those fresh tags must already be interpreted correctly by the
chosen `tm`.  This axiom is the trust boundary behind all downstream
corollaries showing that extern values, pure extern applications, and impure
extern applications produce qualified types that respect `tm`.

### 2.2 Contract B: Guard Provenance for Impure Externs

An impure extern summary may modify memory under a poisoned pc.  If a
memory cell in the post-call state is trusted because it carries an active
guard tag, that trust must trace back to a corresponding guarded-and-active
cell at the same location in the pre-call state.  In other words, impure
extern type summaries may move or preserve guarded trust, but they may not
invent it.

The contract is **guard-only**: the poison analogue is structural (see §1)
and is not part of the axiom surface.
