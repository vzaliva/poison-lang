/-
  ExternRegimeInt.lean - Phase-D foundation (predicate-bearing "open" extern).

  Bottom-up, riskiest-first construction of a predicate-bearing ("open") extern
  trusted-registry instantiation that de-poisons under a true regime policy.
  Lemma order follows doc/extern-regime-impl-plan.md "PHASE D — remaining".

  STATUS (session 5): the two genuinely-uncertain STRUCTURAL divergence points
  vs. the clean noPred spec are VERIFIED here (both build, 0 sorry / 0 axiom):
    (a) `collectAndAllocExternTags_pred` — the allocator yields one fresh tag.
    (b) `applyExternRegimePolicy_singleton` — the regime gains `freshTag ↦ b`,
        so the result regime genuinely changes (ctxAfter ≠ ctx for predicates).
  The cross-run discriminator is resolved in the plan doc: the obligation is
  `agreeValueUnder` via `withPred_true_eq` (output equality), dischargeable by
  the `clean_agree` determinism shape — NOT predicate-satisfaction.

  REMAINING: the full `ExternBoundarySpec` (declFR/callFR/declSingle/callSingle/
  operational) + `TrustedExternEntry` + `TrustedRegistry` + `InputSpec` + the
  top-level `TypeSystemEnforcesFaultRobustness` instantiation.  NOTE: there is NO
  template anywhere — even `PureUnaryCleanIntSpec` (the clean analogue) is never
  assembled into a registry; this would be the first complete FR instantiation.
  The assembly needs the `private` helpers in ExternBoundaryConstructors
  (`stepFRPost_of_parts`, `externBoundarySinglePost_of_parts`, …): either
  un-`private` them (justified — another file now needs them) or build the spec
  inside ExternBoundaryConstructors and expose only the final record.
-/
import LeanProofs.ExternBoundaryProofs

open Std
open LeanPoison

namespace ExternRegimeInt

/-- Divergence point (a): the allocator on a single `guardClosure` predicate
    allocates exactly one fresh tag `nextTag` for index `idx`, advancing to
    `nextTag + 1`.  Contrast `collectAndAllocExternTags_noPred` (rfl, empty map). -/
theorem collectAndAllocExternTags_pred (idx : TagIndex) (nm : Name) (body : Expr) (nextTag : Tag) :
    collectAndAllocExternTags [SyntaxPredicate.guardClosure idx nm body] nextTag
      = .ok (({} : ExtTreeMap TagIndex Tag).insert idx nextTag, nextTag + 1) := by
  rfl

/-- A singleton `ExtTreeMap` lists to a single pair (one node, no ordering
    sensitivity). -/
theorem extTreeMap_toList_singleton (idx : TagIndex) (t : Tag) :
    (({} : ExtTreeMap TagIndex Tag).insert idx t).toList = [(idx, t)] := by
  rfl

/-- Divergence point (b): on the singleton tag mapping, the regime policy
    inserts exactly `freshTag ↦ b` when the policy says `some b` and `freshTag`
    is not already governed.  Contrast the noPred case where the empty mapping
    leaves the regime unchanged (identity). -/
theorem applyExternRegimePolicy_singleton
    (R : Regime) (id : ExternId) (policy : ExternId → Tag → Option Bool)
    (idx : TagIndex) (freshTag : Tag) (b : Bool)
    (hpolicy : policy id freshTag = some b)
    (hnone : R.lookup? freshTag = none) :
    applyExternRegimePolicy R id policy (({} : ExtTreeMap TagIndex Tag).insert idx freshTag)
      = R.insert freshTag b := by
  unfold applyExternRegimePolicy
  rw [extTreeMap_toList_singleton]
  simp only [List.foldl_cons, List.foldl_nil, hpolicy, hnone]

end ExternRegimeInt
