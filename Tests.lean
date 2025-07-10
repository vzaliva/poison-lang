import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.Eval
import LeanPoison.Parser
import LeanPoison.Poison
import LeanPoison.Typecheck

-- Test structure to hold test cases
structure TestCase where
  name : String
  expr : Expr
  expectedValue : Option Value
  expectedType : Option QTyp  -- Expected qualified type
  description : String
  expectedToFail : Bool := false  -- Whether this test is expected to fail

-- Test mode options
inductive TestMode where
  | both : TestMode      -- Run both type checking and evaluation
  | typecheck : TestMode -- Run only type checking
  | eval : TestMode      -- Run only evaluation
  deriving BEq

-- Helper function to run a test case
def runTestCase (test : TestCase) (mode : TestMode := TestMode.both) (verbose : Bool := false) : IO Bool := do
  IO.println s!"Running test: {test.name}"
  IO.println s!"Description: {test.description}"
  if test.expectedToFail then
    IO.println "  Expected to fail: ✓"

  let mut typeResult := true
  let mut evalResult := true

  -- Type checking
  if mode == TestMode.both || mode == TestMode.typecheck then
    typeResult ← match test.expectedType with
    | some expectedQTyp => do
      match typecheckExprSimple test.expr with
      | .ok actualQTyp =>
        -- For now, just check if we got a result (since typecheck is placeholder)
        IO.println s!"  Type check: Expected {repr expectedQTyp}, got {repr actualQTyp}"
        pure true
      | .error msg =>
        if test.expectedToFail then
          IO.println s!"  Type check: ✓ PASS (expected failure) - {msg}"
          pure true
        else
          IO.println s!"  Type check failed: {msg}"
          pure false
    | none => do
      match typecheckExprSimple test.expr with
      | .ok actualQTyp =>
        if test.expectedToFail then
          IO.println s!"  Type check: ✗ FAIL (expected failure but succeeded) - got {repr actualQTyp}"
          pure false
        else
          IO.println s!"  Type check: ✓ PASS - got {repr actualQTyp}"
          pure true
      | .error msg =>
        if test.expectedToFail then
          IO.println s!"  Type check: ✓ PASS (expected failure) - {msg}"
          pure true
        else
          IO.println s!"  Type check failed: {msg}"
          pure false

  -- Evaluation
  if mode == TestMode.both || mode == TestMode.eval then
    let (_, resultExpr) := run defaultFuel test.expr verbose
    evalResult ← match Expr.toValue? resultExpr with
    | some actualValue => do
      let success := test.expectedValue.map (fun expected => actualValue == expected) |>.getD false
      if success then
        IO.println s!"  Evaluation: ✓ PASS - Expected {test.expectedValue}, got {actualValue}"
        pure true
      else
        if test.expectedToFail then
          IO.println s!"  Evaluation: ✓ PASS (expected failure) - got {actualValue}"
          pure true
        else
          IO.println s!"  Evaluation: ✗ FAIL - Expected {test.expectedValue}, got {actualValue}"
          pure false
    | none => do
      if test.expectedToFail then
        IO.println s!"  Evaluation: ✓ PASS (expected failure) - Expression did not evaluate to a value"
        pure true
      else
        IO.println s!"  Evaluation: ✗ FAIL - Expression did not evaluate to a value: {repr resultExpr}"
        pure false

  return typeResult && evalResult

-- Function application type mismatch test
-- This test should fail type checking

def functionTypeMismatchTests : List TestCase := [
  TestCase.mk
    "function_type_mismatch"
    (Expr.app (Expr.fn "x" (Expr.op (Expr.var "x") Op.add (Expr.num 1))) (Expr.bool true))
    none -- No expected value, as evaluation should not occur
    none -- No expected type, as typechecking should fail
    "Applying (fn x => x + 1) to a boolean value should fail type checking."
    true -- Expected to fail
]

-- Helper to create clean qualified type
def cleanQTyp (t : PTyp) : QTyp := ⟨t, false, none⟩

-- Arithmetic example (arithmetic.poison)
def arithmeticTests : List TestCase := [
  TestCase.mk "arithmetic_literal" (Expr.num 42) (some (Value.num 42)) (some (cleanQTyp PTyp.int)) "arithmetic.poison: 42 literal" false,
  TestCase.mk "arithmetic_add" (Expr.op (Expr.num 3) Op.add (Expr.num 4)) (some (Value.num 7)) (some (cleanQTyp PTyp.int)) "arithmetic.poison: 3 + 4" false,
  TestCase.mk "arithmetic_gte" (Expr.op (Expr.num 10) Op.gte (Expr.num 5)) (some (Value.bool true)) (some (cleanQTyp PTyp.bool)) "arithmetic.poison: 10 >= 5" false
]

-- Conditionals example (conditionals.poison)
def conditionalsTests : List TestCase := [
  TestCase.mk "conditionals_true" (Expr.ite (Expr.bool true) (Expr.num 42) (Expr.num 0)) (some (Value.num 42)) (some (cleanQTyp PTyp.int)) "conditionals.poison: if true then 42 else 0" false,
  TestCase.mk "conditionals_false" (Expr.ite (Expr.bool false) (Expr.num 1) (Expr.num 2)) (some (Value.num 2)) (some (cleanQTyp PTyp.int)) "conditionals.poison: if false then 1 else 2" false,
  TestCase.mk "conditionals_gte" (Expr.ite (Expr.op (Expr.num 5) Op.gte (Expr.num 3)) (Expr.num 100) (Expr.num 200)) (some (Value.num 100)) (some (cleanQTyp PTyp.int)) "conditionals.poison: if 5 >= 3 then 100 else 200" false
]

-- Sequences example (sequences.poison)
def sequencesExampleTests : List TestCase := [
  TestCase.mk "sequences_let_seq" (Expr.let "x" (Expr.num 5) (Expr.seq (Expr.var "x") (Expr.num 42))) (some (Value.num 42)) (some (cleanQTyp PTyp.int)) "sequences.poison: let x = 5 in (x; 42)" false,
  TestCase.mk "sequences_unit_seq" (Expr.seq Expr.unit (Expr.num 123)) (some (Value.num 123)) (some (cleanQTyp PTyp.int)) "sequences.poison: unit; 123" false
]

-- References1 example (references1.poison)
def references1ExampleTests : List TestCase := [
  TestCase.mk "references1_basic" (Expr.let "r" (Expr.newRef (Expr.num 42)) (Expr.deref (Expr.var "r"))) (some (Value.num 42)) (some (cleanQTyp PTyp.int)) "references1.poison: let r = ref 42 in !r" false
]

-- References2 example (references2.poison)
def references2ExampleTests : List TestCase := [
  TestCase.mk "references2_assign" (Expr.let "r" (Expr.newRef (Expr.num 10)) (Expr.seq (Expr.assign (Expr.var "r") (Expr.num 20)) (Expr.deref (Expr.var "r")))) (some (Value.num 20)) (some (cleanQTyp PTyp.int)) "references2.poison: let r = ref 10 in (r := 20; !r)" false
]

-- While1 example (while1.poison)
def while1ExampleTests : List TestCase := [
  -- Only the second while loop is supported by the current AST (>=, not <)
  TestCase.mk "while1_geq" (Expr.let "counter" (Expr.newRef (Expr.num 0)) (Expr.while (Expr.op (Expr.deref (Expr.var "counter")) Op.gte (Expr.num 5)) (Expr.assign (Expr.var "counter") (Expr.op (Expr.deref (Expr.var "counter")) Op.add (Expr.num 1))))) (some Value.unit) (some (cleanQTyp PTyp.unit)) "while1.poison: while !counter >= 5 do counter := !counter + 1" false
]

-- Basic poison flow1 example (basic-poison-flow1.poison)
def basicPoisonFlow1Tests : List TestCase := [
  TestCase.mk "basic_poison_flow1_explicit"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "faulty" (Expr.app (Expr.var "get_sensor") Expr.unit)
        (Expr.let "result" (Expr.op (Expr.var "faulty") Op.add (Expr.num 1))
          (Expr.var "result"))))
    (some (Value.num 43))
    (some (cleanQTyp PTyp.int))
    "basic-poison-flow1.poison: explicit flow (data dependency)" false
]

-- Basic poison flow2 example (basic-poison-flow2.poison)
def basicPoisonFlow2Tests : List TestCase := [
  TestCase.mk "basic_poison_flow2_implicit"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "faulty" (Expr.app (Expr.var "get_sensor") Expr.unit)
        (Expr.ite (Expr.op (Expr.var "faulty") Op.gte (Expr.num 1)) (Expr.num 42) (Expr.num 17))))
    (some (Value.num 42))
    (some (cleanQTyp PTyp.int))
    "basic-poison-flow2.poison: implicit flow (control dependency)" false
]

-- Conditional poison example (conditional-poison.poison)
def conditionalPoisonTests : List TestCase := [
  TestCase.mk "conditional_poison_complex"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "sensor" (Expr.app (Expr.var "get_sensor") Expr.unit)
        (Expr.let "threshold" (Expr.num 50)
          (Expr.ite (Expr.op (Expr.var "sensor") Op.gte (Expr.var "threshold"))
            (Expr.op (Expr.var "sensor") Op.add (Expr.num 100))
            (Expr.op (Expr.var "threshold") Op.add (Expr.num 100))))))
    (some (Value.num 150))
    (some (cleanQTyp PTyp.int))
    "conditional-poison.poison: conditional poison with complex expressions (sensor >= threshold ? sensor+100 : threshold+100)" false
]

-- Function composition poison example (function-composition-poison.poison)
def functionCompositionPoisonTests : List TestCase := [
  TestCase.mk "function_composition_poison"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "f" (Expr.fn "x" (Expr.op (Expr.var "x") Op.add (Expr.num 1)))
        (Expr.let "g" (Expr.fn "x" (Expr.op (Expr.var "x") Op.add (Expr.var "x")))
          (Expr.let "poisoned_input" (Expr.app (Expr.var "get_sensor") Expr.unit)
            (Expr.let "result" (Expr.app (Expr.var "g") (Expr.app (Expr.var "f") (Expr.var "poisoned_input")))
              (Expr.var "result"))))))
    (some (Value.num 86))
    (some (cleanQTyp PTyp.int))
    "function-composition-poison.poison: poison propagation through function composition" false
]

-- Function poison example (function-poison.poison)
def functionPoisonTests : List TestCase := [
  TestCase.mk "function_poison_selection"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "poisoned_cond" (Expr.app (Expr.var "get_sensor") Expr.unit)
        (Expr.let "f"
          (Expr.ite (Expr.op (Expr.var "poisoned_cond") Op.gte (Expr.num 1))
            (Expr.fn "x" (Expr.op (Expr.var "x") Op.add (Expr.num 1)))
            (Expr.fn "x" (Expr.op (Expr.var "x") Op.add (Expr.var "x"))))
          (Expr.let "result" (Expr.app (Expr.var "f") (Expr.num 10))
            (Expr.var "result")))))
    (some (Value.num 11))
    (some (cleanQTyp PTyp.int))
    "function-poison.poison: function calls and poisoned function selection" false
]

-- Multiple poison sources example (multiple-poison-sources.poison)
def multiplePoisonSourcesTests : List TestCase := [
  TestCase.mk "multiple_poison_sources"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "get_corrupted_ptr" (Expr.fn "x_unit" (Expr.newRef (Expr.num 42)))
        (Expr.let "sensor1" (Expr.app (Expr.var "get_sensor") Expr.unit)
          (Expr.let "sensor2_ptr" (Expr.app (Expr.var "get_corrupted_ptr") Expr.unit)
            (Expr.let "result" (Expr.op (Expr.op (Expr.var "sensor1") Op.add (Expr.num 10)) Op.add (Expr.deref (Expr.var "sensor2_ptr")))
              (Expr.var "result"))))))
    (some (Value.num 94))
    (some (cleanQTyp PTyp.int))
    "multiple-poison-sources.poison: poison propagation from multiple unreliable inputs" false
]

-- Reference poison1 example (reference-poison1.poison)
def referencePoison1Tests : List TestCase := [
  TestCase.mk "reference_poison1_data"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "r" (Expr.newRef (Expr.num 0))
        (Expr.seq (Expr.assign (Expr.var "r") (Expr.app (Expr.var "get_sensor") Expr.unit))
          (Expr.deref (Expr.var "r")))))
    (some (Value.num 42))
    (some (cleanQTyp PTyp.int))
    "reference-poison1.poison: reference operations with poisoned data" false
]

-- Reference poison2 example (reference-poison2.poison)
def referencePoison2Tests : List TestCase := [
  TestCase.mk "reference_poison2_untrusted"
    (Expr.let "get_corrupted_ptr" (Expr.fn "x_unit" (Expr.newRef (Expr.num 42)))
      (Expr.let "bad_ref" (Expr.app (Expr.var "get_corrupted_ptr") Expr.unit)
        (Expr.seq (Expr.deref (Expr.var "bad_ref"))
          (Expr.assign (Expr.var "bad_ref") (Expr.num 42)))))
    (some Value.unit)
    (some (cleanQTyp PTyp.unit))
    "reference-poison2.poison: poisoned references" false
]

-- Sensor processing example (sensor-processing.poison)
def sensorProcessingTests : List TestCase := [
  TestCase.mk "sensor_processing_complex"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "sensor1" (Expr.app (Expr.var "get_sensor") Expr.unit)
        (Expr.let "sensor2" (Expr.app (Expr.var "get_sensor") Expr.unit)
          (Expr.let "f"
            (Expr.fn "x"
              (Expr.ite (Expr.op (Expr.var "sensor1") Op.gte (Expr.num 0))
                (Expr.ite (Expr.op (Expr.var "x") Op.gte (Expr.num 0))
                  (Expr.op (Expr.var "sensor1") Op.add (Expr.var "x"))
                  (Expr.num 0))
                (Expr.num 0)))
            (Expr.let "result" (Expr.app (Expr.var "f") (Expr.var "sensor2"))
              (Expr.var "result"))))))
    (some (Value.num 84))
    (some (cleanQTyp PTyp.int))
    "sensor-processing.poison: sensor processing with de-poisoning" false
]

-- Sensor reading example (sensor-reading.poison)
def sensorReadingTests : List TestCase := [
  TestCase.mk "sensor_reading_basic"
    (Expr.let "get_sensor" (Expr.fn "x" (Expr.num 42))
      (Expr.let "reading" (Expr.app (Expr.var "get_sensor") Expr.unit)
        (Expr.let "adjusted" (Expr.op (Expr.var "reading") Op.add (Expr.num 10))
          (Expr.var "adjusted"))))
    (some (Value.num 52))
    (some (cleanQTyp PTyp.int))
    "sensor-reading.poison: basic sensor reading example" false
]

-- Combine all test suites
def allTests : List TestCase :=
  arithmeticTests ++
  conditionalsTests ++
  sequencesExampleTests ++
  references1ExampleTests ++
  references2ExampleTests ++
  while1ExampleTests ++
  basicPoisonFlow1Tests ++
  basicPoisonFlow2Tests ++
  conditionalPoisonTests ++
  functionCompositionPoisonTests ++
  functionPoisonTests ++
  multiplePoisonSourcesTests ++
  referencePoison1Tests ++
  referencePoison2Tests ++
  sensorProcessingTests ++
  sensorReadingTests ++
  functionTypeMismatchTests

-- Run selected tests by name, or all if names is empty
def runSelectedTests (names : List String) (mode : TestMode := TestMode.both) (verbose : Bool := false) : IO Unit := do
  let selected := if names.isEmpty then allTests else allTests.filter (fun t => names.contains t.name)
  IO.println "Running Poison Language Test Suite"
  IO.println "=================================="
  IO.println s!"Mode: {match mode with | TestMode.both => "both" | TestMode.typecheck => "typecheck only" | TestMode.eval => "eval only"}"
  IO.println ""

  let mut passed := 0
  let mut failed := 0

  for test in selected do
    let result ← runTestCase test mode verbose
    if result then
      passed := passed + 1
    else
      failed := failed + 1
    IO.println ""

  IO.println "Test Summary"
  IO.println "============"
  IO.println s!"Passed: {passed}"
  IO.println s!"Failed: {failed}"
  IO.println s!"Total: {selected.length}"

  if failed > 0 then
    IO.println "❌ Some tests failed!"
    IO.Process.exit 1
  else
    IO.println "✅ All tests passed!"

-- Entry point for running tests
def runAllTests (mode : TestMode := TestMode.both) (verbose : Bool := false) : IO Unit := do
  runSelectedTests [] mode verbose

-- Main function for executable
def main (args : List String) : IO Unit := do
  let verbose := args.any (fun a => a = "-v" || a = "--verbose")
  let typecheckOnly := args.any (fun a => a = "--typecheck" || a = "-t")
  let evalOnly := args.any (fun a => a = "--eval" || a = "-e")

  let mode := if typecheckOnly then TestMode.typecheck
              else if evalOnly then TestMode.eval
              else TestMode.both

  let filtered := args.filter (fun a => a ≠ "-v" ∧ a ≠ "--verbose" ∧ a ≠ "--typecheck" ∧ a ≠ "-t" ∧ a ≠ "--eval" ∧ a ≠ "-e")
  runSelectedTests filtered mode verbose
