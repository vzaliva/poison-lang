import LeanProofs.FaultRobustnessProofs
import LeanProofs.ExternCallsWitnessClosed
import LeanProofs.ExternCallsWitnessCell
import LeanProofs.ExternCallsWitnessCellClosed
import LeanProofs.ExternCallsWitnessVal
import LeanProofs.PredSatLawsCellWitness
import LeanProofs.GuardCapsBelowWitness
import LeanProofs.ExternCallsWitnessValCell
import LeanProofs.ExternCallsWitnessValCellWrite

-- Expected: only Lean's standard axioms propext, Classical.choice, Quot.sound
-- (no sorryAx, no project-specific axioms).
#print axioms TypeSystemEnforcesFaultRobustness
#print axioms TypeSystemEnforcesFaultRobustness_allCtx

-- The premises on extern calls for the witness programs, and the theorem applied
-- to them with every premise proved.
#print axioms ExternCallsWitness.Wrapper.prog_real
#print axioms ExternCallsWitness.Wrapper.prog_bad
#print axioms ExternCallsWitness.Skipped.prog_real
#print axioms ExternCallsWitness.Skipped.prog_bad
#print axioms ExternCallsWitness.TwoRuns.agree_case
#print axioms ExternCallsWitness.TwoCalls.two_calls_case
#print axioms ExternCallsWitness.Cell.cell_case
#print axioms ExternCallsWitness.readSpec
#print axioms ExternCallsWitness.wrapper_closed
#print axioms ExternCallsWitness.skipped_closed
#print axioms ExternCallsWitness.twoRuns_closed
#print axioms ExternCallsWitness.twoCalls_closed

-- A trusted entry for an extern with an effect on its argument's cell, and the
-- theorem applied to programs that call it.
#print axioms ExternCallsWitness.Cell.rdSpec
#print axioms ExternCallsWitness.Cell.cell_closed_4_5
#print axioms ExternCallsWitness.Cell.ReadBack.readBack_case
#print axioms ExternCallsWitness.Cell.ReadBack.same_return_4_5

-- A trusted entry for a guarded extern value, and the theorem applied to a
-- program that declares it, under both values of its tag.
#print axioms ExternCallsWitness.Val.vSpec
#print axioms ExternCallsWitness.Val.val_case
#print axioms ExternCallsWitness.Val.true_5
#print axioms ExternCallsWitness.Val.false_neg3

-- A relation for a guard that reads a cell meets the laws, and the match is
-- exercised; guards that are never selected admit a constant relation.
#print axioms PredSatLawsCellWitness.cellSat_lawful
#print axioms PredSatLawsCellWitness.match_exercised
#print axioms PredSatLawsCellWitness.TwoTargets.lawful
#print axioms PredSatLawsCellWitness.DerefArg.lawful
#print axioms PredSatLawsCellWitness.DerefArg.footprint_forces_constant

-- A sufficient condition for the start condition `GuardCapsBelow`, and two
-- contexts where the converse fails.
#print axioms GuardCapsBelowWitness.guardCapsBelow_of_guardLocsBelow
#print axioms GuardCapsBelowWitness.converse_fails
#print axioms GuardCapsBelowWitness.converse_fails_argQ

-- A trusted entry for an extern value whose guard reads a cell, and the theorem
-- applied to a program that declares it and tests the guard.
#print axioms ExternCallsWitness.ValCell.vSpec
#print axioms ExternCallsWitness.ValCell.cellSat_lawful
#print axioms ExternCallsWitness.ValCell.typing_case
#print axioms ExternCallsWitness.ValCell.same_return
#print axioms ExternCallsWitness.ValCell.true_7
#print axioms ExternCallsWitness.ValCell.false_3

-- The same guarded value with a write to another cell between the declaration and
-- the test: the guard stays in the regime and the theorem applies.
#print axioms ExternCallsWitness.ValCellWrite.typing_case
#print axioms ExternCallsWitness.ValCellWrite.same_return
#print axioms ExternCallsWitness.ValCellWrite.true_7
#print axioms ExternCallsWitness.ValCellWrite.false_3
#print axioms ExternCallsWitness.ValCellWrite.write_a_poisoned
