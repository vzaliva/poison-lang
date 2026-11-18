import LeanProofs.FaultRobustnessProofs
import LeanProofs.ExternCallsWitnessClosed
import LeanProofs.ExternCallsWitnessCell
import LeanProofs.ExternCallsWitnessCellClosed
import LeanProofs.ExternCallsWitnessVal
import LeanProofs.ExternCallsWitnessInt
import LeanProofs.ExternCallsWitnessIntCall
import LeanProofs.ExternCallsWitnessIntCallFalse
import LeanProofs.ExternCallsWitnessCallInBody

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

-- A trusted entry for an extern value whose guard reads a let-bound integer, and
-- the theorem applied to a program that tests the value against that variable.
#print axioms ExternCallsWitness.IntGuard.loSpec
#print axioms ExternCallsWitness.IntGuard.same_return
#print axioms ExternCallsWitness.IntGuard.true_5
#print axioms ExternCallsWitness.IntGuard.fails_0

-- A trusted entry for an extern function whose result guard reads a let-bound
-- integer, and the theorem applied to a program that calls it and tests the
-- result against that variable.
#print axioms ExternCallsWitness.IntCall.gSpec
#print axioms ExternCallsWitness.IntCall.same_return
#print axioms ExternCallsWitness.IntCall.true_5
#print axioms ExternCallsWitness.IntCall.fails_0

-- The program of the extern-function witness under a false tag, and the
-- theorem applied to it.
#print axioms ExternCallsWitness.IntCallFalse.gSpec
#print axioms ExternCallsWitness.IntCallFalse.typed_clean
#print axioms ExternCallsWitness.IntCallFalse.call_reached
#print axioms ExternCallsWitness.IntCallFalse.laws_program
#print axioms ExternCallsWitness.IntCallFalse.tests
#print axioms ExternCallsWitness.IntCallFalse.view_needed
#print axioms ExternCallsWitness.IntCallFalse.match_iff
#print axioms ExternCallsWitness.IntCallFalse.match_iff_lawful
#print axioms ExternCallsWitness.IntCallFalse.no_premises_ge
#print axioms ExternCallsWitness.IntCallFalse.agree
#print axioms ExternCallsWitness.IntCallFalse.same_return
#print axioms ExternCallsWitness.IntCallFalse.false_5
#print axioms ExternCallsWitness.IntCallFalse.fails_10
#print axioms ExternCallsWitness.CallInBody.gSpec
#print axioms ExternCallsWitness.CallInBody.typed_clean
#print axioms ExternCallsWitness.CallInBody.call_reached
#print axioms ExternCallsWitness.CallInBody.laws_program
#print axioms ExternCallsWitness.CallInBody.tests
#print axioms ExternCallsWitness.CallInBody.view_needed
#print axioms ExternCallsWitness.CallInBody.match_iff
#print axioms ExternCallsWitness.CallInBody.match_iff_lawful
#print axioms ExternCallsWitness.CallInBody.no_premises_lt
#print axioms ExternCallsWitness.CallInBody.agree
#print axioms ExternCallsWitness.CallInBody.same_return
#print axioms ExternCallsWitness.CallInBody.true_5
#print axioms ExternCallsWitness.CallInBody.fails_0
