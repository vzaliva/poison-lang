# Application Fault-Robustness Proof: Current Blockers

## Blockers

- **Body context instantiation gap**: `applyFnTClosure` builds the body typing context from `VarTypeEnv.ofCaptured σcap` plus the argument. The runtime body evaluation uses the closure's captured `VarEnv`. There is no lemma that turns `agreeCapturedEnv` (clean-only) or `valueHasETyp` for closures into `runtimeInstantiatesCtx` for this body context.
- **Join lifting for results**: `joinTypeResults` changes `memEnv'`, `tagEnv'`, `nextLoc'`, `nextTag'`, and potentially the result qualifier. There are no lemmas showing that `runtimeInstantiatesCtx`, `agreeOnClean`, and `regimeConsistentWithCtx` are preserved when moving from a single closure result to the joined result.
- **Closure-to-typing alternative alignment**: `hfun_agree` only states agreement of runtime closures at `res1.qualType`. The proof still needs a link from the runtime closure to a specific `FnTClosure` in the typing list in order to extract the corresponding body typing result.

## Potential directions

- **Strengthen closure typing**: extend `valueHasETyp` for closures to include instantiation of the captured typing environment, enabling direct derivation of `runtimeInstantiatesCtx` for the body context.
- **Strengthen captured-environment agreement**: add a lemma that `agreeCapturedEnv` implies `valueHasETyp` for all captured entries (or require it as an additional premise), not only for clean entries.
- **Provide join preservation lemmas**: prove that `runtimeInstantiatesCtx`, `agreeOnClean`, and `regimeConsistentWithCtx` are monotone under `joinTypeResults`, and that individual closure results embed into the joined result.
- **Restate the helper lemma**: add explicit premises for body-context instantiation and agreement so the application proof can proceed without new global invariants.
