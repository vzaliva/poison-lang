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
