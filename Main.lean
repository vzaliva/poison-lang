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
def handleEvalResult (result : Except String (Config × Value)) (verbose : Bool) : IO UInt32 := do
  match result with
  | .ok (config, value) =>
      printValue value
      printFinalState config verbose
      return (0 : UInt32)
  | .error msg=>
      IO.println s!"Runtime error: {msg}"
      return (1 : UInt32)

def evalProgram (input : String) (verbose : Bool) : IO UInt32 := do
  match parse input with
  | Except.ok xmlElement =>

    match xmlToExpr xmlElement with
    | Except.ok expr =>
      let resultType := typecheckProgram expr false
      if resultType.startsWith "Type error:" then
        IO.println s!"Type checking error: {resultType.drop 11}"
      else
        IO.println s!"Type checking passed: {resultType}"
      let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0, false⟩
      let result <- LeanPoison.beval defaultFuel initialConfig expr verbose
      handleEvalResult result verbose

    | Except.error err =>
      IO.println s!"Error while building expression tree: {err}"
      return (1 : UInt32)

  | Except.error e => IO.println s!"Parse error: {e}"
                      return (1 : UInt32)

-- Read and evaluate a file
def runFile (filename : String) (verbose : Bool)  : IO UInt32 := do
  try
    let xmlStr ← runTreeSitterXml filename
    IO.println s!"Evaluating file: {filename}"
    IO.println ""
    evalProgram xmlStr verbose
  catch e =>
    IO.println s!"Error reading file {filename}: {e}"
    return (1 : UInt32)
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
      | (newConfig, resultExpr) =>
        match resultExpr.toValue? with
        | some v =>
            IO.println s!"Result: {v}"
            IO.println s!"Memory: {newConfig.memory}"
        | _ =>
            IO.println s!"Not fully evaluated: {repr resultExpr}"
        IO.FS.removeFile tmpPath
        replLoop newConfig tmpPath

    catch e =>
      IO.eprintln s!"Error: {e}"
      replLoop config tmpPath
-------------------------------------------------------------------------------
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
          IO.println s!"Type checking error: {resultType.drop 11}"
        else
          IO.println s!"Type checking passed: {resultType}"
        IO.println ""
        let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0, false⟩
        let result <-  LeanPoison.beval defaultFuel initialConfig expr true
        handleEvalResult result true

    catch e =>
      IO.println s!"Error reading file {filename}: {e}"
      return (1 : UInt32)

  | ["--repl"] =>
    IO.println s!"Poison {versionNo} - Tufts University."
    IO.println "Type :quit to exit."
    IO.println "Enter a blank line after an expression to evaluate it."
    let tmp ← IO.Process.output { cmd := "mktemp", args := #["--tmpdir", "repl-XXXXXX.poison"] }
    let tmpPath := tmp.stdout.trim
    let initialConfig := ⟨ emptyMemory, emptyVarEnv,  0, false ⟩
    replLoop initialConfig tmpPath


  | [filename] =>
    -- One argument: evaluate file
    runFile filename false

  | _ =>
    -- Too many arguments: show usage
    IO.println "Usage:"
    IO.println "  poison-interpreter --repl"
    IO.println "  poison-interpreter [--verbose] <file>"
    IO.println "  poison-interpreter <file>"
    return (1 : UInt32)
