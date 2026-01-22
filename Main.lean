import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanPoison.Parser
import LeanPoison.Typecheck
import Lean.Data.Xml.Parser
import Init.System.IO
import Lean
open Lean IO
open Lean Xml

/-!
## Exit Code Table:

| Scenario                                    | Type Check Analysis | Type Check Result | Evaluation    | Exit Code |
|---------------------------------------------|---------------------|-------------------|---------------|-----------|
| Well-typed, runs successfully               | ✓ Completes         | Pass              | ✓ Success     | 0         |
| Type error detected (e.g., type mismatch)   | ✓ Completes         | Type error found  | (skipped)     | 0         |
| Parse error                                 | ✗ Failed            | N/A               | (skipped)     | 2         |
| AST construction error (XML→Expr)           | ✗ Failed            | N/A               | (skipped)     | 3         |
| Type checker out of fuel                    | ✗ Incomplete        | Out of fuel       | (skipped)     | 4         |
| File I/O error                              | ✗ Failed            | N/A               | (skipped)     | 5         |
| Well-typed, runtime error                   | ✓ Completes         | Pass              | ✗ Error       | 6         |
| Well-typed, eval out of fuel                | ✓ Completes         | Pass              | ✗ Out of fuel | 7         |
| Invalid arguments                           | N/A                 | N/A               | (skipped)     | 1         |

## Rationale:
Exit code 0 indicates that the analysis tool itself worked correctly, regardless of whether
the program being analyzed is well-typed. This follows the convention of compilers that
return 0 even when reporting type errors, since successfully finding errors is a success
for the tool.
-/

-- Default fuel amount for evaluation
def defaultFuel : Nat := 1000
-- Language Version No
def versionNo := "1.0"

-- Helper function to print a value
def printValue (v : Value) : IO Unit := do
  match v with
  | Value.num n => IO.println s!"Result: {n}"
  | Value.bool b => IO.println s!"Result: {b}"
  | Value.unit => IO.println s!"Result: unit"
  | Value.str s => IO.println s!"Result: {s}"
  | Value.loc l => IO.println s!"Result: loc {l}"
  | Value.closure _ _ _ => IO.println s!"Result: <closure>"
  | Value.peClosure _ _ _ => IO.println s!"Result: <pure closure>"

-- Helper function to print final state
def printFinalState (config : Config) (verbose : Bool) : IO Unit := do
  if verbose then
    IO.println s!"Final state:"
    IO.println ("Variable environment: " ++ toString config.varEnv)
    IO.println s!"  Memory: {repr config.memory}"
  else
    IO.println s!"Final state:"
    IO.println s!"  Variable environment: {repr config.varEnv}"
    IO.println s!"  Memory: {repr config.memory}"

-- Helper function to handle evaluation results
def handleEvalResult (result : LeanPoison.EvalResult) (verbose : Bool) : IO UInt32 := do
  match result with
  | .success config value =>
      printValue value
      printFinalState config verbose
      return (0 : UInt32)
  | .outOfFuel =>
      IO.println "Error: out of fuel (program may diverge)"
      return (7 : UInt32)  -- Exit code 7: Evaluation out of fuel
  | .runtimeError msg =>
      IO.println s!"Runtime error: {msg}"
      return (6 : UInt32)  -- Exit code 6: Runtime error
  | .ioForbidden =>
      IO.println "Error: IO operation attempted in ioFree mode"
      return (6 : UInt32)  -- Exit code 6: Runtime error (IO forbidden)

def evalProgram (input : String) (verbose : Bool) : IO UInt32 := do
  match parse input with
  | Except.ok xmlElement =>

    match xmlToExpr xmlElement with
    | Except.ok expr =>
      let resultType := typecheckProgram expr false
      if resultType.startsWith "Type error:" then
        let errorMsg := resultType.drop 11
        IO.println s!"Type checking error: {errorMsg}"
        -- "Out of fuel" means analysis couldn't complete (exit 4)
        -- Other type errors mean analysis succeeded in finding errors (exit 0)
        if errorMsg.trim == "Out of fuel" then
          return (4 : UInt32)  -- Exit code 4: Type checker out of fuel
        else
          return (0 : UInt32)  -- Exit code 0: Type error successfully found
      else
        IO.println s!"Type checking passed: {resultType}"
        let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0, false⟩
        let result <- LeanPoison.beval .normal defaultFuel initialConfig expr verbose
        handleEvalResult result verbose

    | Except.error err =>
      IO.println s!"Error while building expression tree: {err}"
      return (3 : UInt32)  -- Exit code 3: AST construction error

  | Except.error e => IO.println s!"Parse error: {e}"
                      return (2 : UInt32)  -- Exit code 2: Parse error

-- Read and evaluate a file
def runFile (filename : String) (verbose : Bool)  : IO UInt32 := do
  try
    let xmlStr ← runTreeSitterXml filename
    IO.println s!"Evaluating file: {filename}"
    IO.println ""
    evalProgram xmlStr verbose
  catch e =>
    IO.println s!"Error reading file {filename}: {e}"
    return (5 : UInt32)  -- Exit code 5: File I/O error
-------------------------------------------------------------------------------
partial def readMultiline (acc : String := "") : IO String := do
  IO.print " > "
  let unline ← IO.getStdin
  let line <- unline.getLine
  let newAcc := acc ++ "\n" ++ line
  if line.trim.isEmpty then
    return newAcc.trim
  else
    readMultiline newAcc
  ----------------------------------------------------------------------------
partial def replLoop (config : Config) (tmpPath : String) : IO UInt32 := do

  let trimmed ← readMultiline
  if trimmed == ":quit" then
    IO.println "Goodbye!"
    return (0 : UInt32)
  else

    IO.FS.writeFile tmpPath trimmed
    try
      let expr ← parsePoisonFile tmpPath
      match <- LeanPoison.runBig defaultFuel expr false with
      | .success newConfig v =>
        IO.println s!"Result: {v}"
        IO.println s!"Memory: {newConfig.memory}"
        IO.FS.removeFile tmpPath
        replLoop newConfig tmpPath
      | .outOfFuel =>
        IO.FS.removeFile tmpPath
        replLoop config tmpPath
      | .runtimeError _ =>
        IO.FS.removeFile tmpPath
        replLoop config tmpPath
      | .ioForbidden =>
        IO.FS.removeFile tmpPath
        replLoop config tmpPath

    catch e =>
      IO.eprintln s!"Error: {e}"
      replLoop config tmpPath
-------------------------------------------------------------------------------
-- Print usage message and exit codes
def printUsage : IO Unit := do
  IO.println "Usage:"
  IO.println "  poison-interpreter --repl"
  IO.println "  poison-interpreter [--verbose] <file>"
  IO.println "  poison-interpreter <file>"
  IO.println "  poison-interpreter --help"
  IO.println ""
  IO.println "Exit Codes:"
  IO.println "  0  Success (including successful detection of type errors)"
  IO.println "  1  Usage error (wrong command-line arguments)"
  IO.println "  2  Parse error (syntax error in source)"
  IO.println "  3  AST construction error (internal parser error)"
  IO.println "  4  Type checker out of fuel (analysis couldn't complete)"
  IO.println "  5  File I/O error (can't read file)"
  IO.println "  6  Runtime error (evaluation failed)"
  IO.println "  7  Evaluation out of fuel (divergence)"
  IO.println ""
  IO.println "Note: Exit code 0 indicates that the analysis tool itself worked correctly,"
  IO.println "regardless of whether the program being analyzed is well-typed. This follows"
  IO.println "the convention of compilers that return 0 even when reporting type errors,"
  IO.println "since successfully finding errors is a success for the tool."

def main (args : List String) : IO UInt32 := do
  match args with

  | ["--verbose", filename] =>
    -- Verbose mode
    try
      let ExprTree ← parsePoisonFile filename
      IO.println s!"Evaluating file: {filename} (verbose mode)"
      IO.println ""
      match ExprTree with
      | expr =>
       let resultType := typecheckProgram expr true
        if resultType.startsWith "Type error:" then
          let errorMsg := resultType.drop 11
          IO.println s!"Type checking error: {errorMsg}"
          IO.println ""
          -- "Out of fuel" means analysis couldn't complete (exit 4)
          -- Other type errors mean analysis succeeded in finding errors (exit 0)
          if errorMsg.trim == "Out of fuel" then
            return (4 : UInt32)  -- Exit code 4: Type checker out of fuel
          else
            return (0 : UInt32)  -- Exit code 0: Type error successfully found
        else
          IO.println s!"Type checking passed: {resultType}"
          IO.println ""
          let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0, false⟩
          let result <-  LeanPoison.beval .normal defaultFuel initialConfig expr true
          handleEvalResult result true

    catch e =>
      IO.println s!"Error reading file {filename}: {e}"
      return (5 : UInt32)  -- Exit code 5: File I/O error

  | ["--repl"] =>
    IO.println s!"Poison {versionNo} - Tufts University."
    IO.println "Type :quit to exit."
    IO.println "Enter a blank line after an expression to evaluate it."
    let tmp ← IO.Process.output { cmd := "mktemp", args := #["--tmpdir", "repl-XXXXXX.poison"] }
    let tmpPath := tmp.stdout.trim
    let initialConfig := ⟨ emptyMemory, emptyVarEnv,  0, false ⟩
    replLoop initialConfig tmpPath

  | ["--help"] =>
    -- Show usage and exit codes
    printUsage
    return (0 : UInt32)

  | [filename] =>
    -- One argument: evaluate file
    runFile filename false

  | _ =>
    -- Too many arguments: show usage
    printUsage
    return (1 : UInt32)
