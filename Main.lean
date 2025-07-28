import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.Eval
import LeanPoison.Parser
import Lean.Data.Xml.Parser
import Init.System.IO
open Lean IO
open Lean Xml

def evalProgram (input : String) : IO Unit := do
  match parse input with
  | Except.ok xmlElement =>

    match xmlToExpr xmlElement with
    | Except.ok expr =>
      let (config, resultExpr) :=run defaultFuel expr
      match Expr.toValue? resultExpr with
      | some v =>
        match v with
        | Value.num n => IO.println s!"Result: {n}"
        | Value.bool b => IO.println s!"Result: {b}"
        | Value.unit => IO.println s!"Result: unit"
        | Value.loc l => IO.println s!"Result: loc {l}"
        | Value.closure _ _ _ => IO.println s!"Result: <closure>"
        | Value.peClosure _ _ _ => IO.println s!"Result: <pure closure>"
      | none =>
        IO.println "Expression is not fully evaluated."
        IO.println s!"Remaining: {repr resultExpr}"
      -- Print final state
      IO.println s!"Final state:"
      IO.println s!"  Variable environment: <function>"
      IO.println s!"  Memory: {repr config.memory}"
    | Except.error err =>
      IO.println s!"Error while building expression tree: {err}"

  | Except.error e => IO.println s!"Parse error: {e}"

-- Read and evaluate a file
def runFile (filename : String) : IO Unit := do
  try
    let xmlStr ← runTreeSitterXml filename
    IO.println s!"Evaluating file: {filename}"
    IO.println ""
    evalProgram xmlStr
  catch e =>
    IO.println s!"Error reading file {filename}: {e}"
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
partial def replLoop (config : Config) : IO Unit := do

  let trimmed ← readMultiline
  if trimmed == ":quit" then
    IO.println "Goodbye!"

  else
    let tempFile := (System.FilePath.join (← IO.currentDir) "ReplInput.poison").toString

    IO.FS.writeFile tempFile trimmed
    try

      let expr ← parsePoisonFile tempFile
      let (newConfig, resultExpr) := eval defaultFuel config expr false
      match Expr.toValue? resultExpr with
      | some v =>
          IO.println s!"Result: {v}"
          IO.println s!"Memory: {newConfig.memory}"

      | none =>
          IO.println s!"Not fully evaluated: {repr resultExpr}"
      replLoop newConfig
    catch e =>
      IO.eprintln s!"Error: {e}"
      replLoop config

-------------------------------------------------------------------------------
def main (args : List String) : IO Unit := do
  match args with
  | ["--verbose", filename] =>
    -- Verbose mode: evaluate file with step-by-step output
    try
      let ExprTree ← parsePoisonFile filename
      IO.println s!"Evaluating file: {filename} (verbose mode)"
      IO.println ""
      match ExprTree with
      | expr =>
        let (config, resultExpr) := run defaultFuel expr true  -- verbose = true
        match Expr.toValue? resultExpr with
        | some v =>
          match v with
          | Value.num n => IO.println s!"Result: {n}"
          | Value.bool b => IO.println s!"Result: {b}"
          | Value.unit => IO.println s!"Result: unit"
          | Value.loc l => IO.println s!"Result: loc {l}"
          | Value.closure _ _ _ => IO.println s!"Result: <closure>"
          | Value.peClosure _ _ _ => IO.println s!"Result: <pure closure>"
        | none =>
          IO.println "Expression is not fully evaluated."
          IO.println s!"Remaining: {repr resultExpr}"
        IO.println s!"Final state:"
        IO.println s!"  Variable environment: <function>"
        IO.println s!"  Memory: {repr config.memory}"
    catch e =>
      IO.println s!"Error reading file {filename}: {e}"

  | ["--repl"] =>
    IO.println "Poison 1.0 - Tufts University."
    IO.println "Type :quit to exit."
    IO.println "Enter a blank line after an expression to evaluate it."
    let initialConfig := ⟨ emptyMemory, emptyVarEnv,  0 ⟩
    replLoop initialConfig

  | [filename] =>
    -- One argument: evaluate file
    runFile filename


  | _ =>
    -- Too many arguments: show usage
    IO.println "Usage:"
    IO.println "  poison-interpreter --repl          # Runs read-eval-print loop"
    IO.println "  poison-interpreter <file>           # Evaluate expressions from file"
    IO.println "  poison-interpreter --verbose <file> # Evaluate with step-by-step output"
