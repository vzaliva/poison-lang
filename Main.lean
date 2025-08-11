import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.Eval
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

def evalProgram (input : String) : IO Int := do
  match parse input with
  | Except.ok xmlElement =>

    match xmlToExpr xmlElement with
    | Except.ok expr =>
      let (config, resultExpr) <- run defaultFuel expr
      let resultType := typecheckProgram expr
      match Expr.toValue? resultExpr with
      | some v =>
        match v with
        | Value.num n => IO.println s!"Result: {n}"
        | Value.bool b => IO.println s!"Result: {b}"
        | Value.unit => IO.println s!"Result: unit"
        | Value.str s => IO.println (s!"Result: " ++ s)
        | Value.loc l => IO.println s!"Result: loc {l}"
        | Value.closure _ _ _ => IO.println s!"Result: <closure>"
        | Value.peClosure _ _ _ => IO.println s!"Result: <pure closure>"
        IO.println resultType
        IO.println s!"Final state:"
        IO.println s!"  Variable environment: <function>"
        IO.println s!"  Memory: {repr config.memory}"
        return 0
      | none =>
        IO.println "Expression is not fully evaluated."
        IO.println s!"Remaining: {repr resultExpr}"
      -- Print final state
        IO.println s!"Final state:"
        IO.println s!"  Variable environment: <function>"
        IO.println s!"  Memory: {repr config.memory}"
         return 1

    | Except.error err =>
      IO.println s!"Error while building expression tree: {err}"
      return 1

  | Except.error e => IO.println s!"Parse error: {e}"
                      return 1

-- Read and evaluate a file
def runFile (filename : String) : IO Int := do
  try
    let xmlStr ← runTreeSitterXml filename
    IO.println s!"Evaluating file: {filename}"
    IO.println ""
    evalProgram xmlStr
  catch e =>
    IO.println s!"Error reading file {filename}: {e}"
    return 1
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
partial def replLoop (config : Config) (tmpPath : String) : IO Int := do

  let trimmed ← readMultiline
  if trimmed == ":quit" then
    IO.println "Goodbye!"
    return 0
  else

    IO.FS.writeFile tmpPath trimmed
    try
      let expr ← parsePoisonFile tmpPath
      let (newConfig, resultExpr) <- eval defaultFuel config expr false
      match Expr.toValue? resultExpr with
      | some v =>
          IO.println s!"Result: {v}"
          IO.println s!"Memory: {newConfig.memory}"
      | none =>
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
    -- Verbose mode: evaluate file with step-by-step output
    try
      let ExprTree ← parsePoisonFile filename
      IO.println s!"Evaluating file: {filename} (verbose mode)"
      IO.println ""
      match ExprTree with
      | expr =>
        let (config, resultExpr) <- run defaultFuel expr true  -- verbose = true
        match Expr.toValue? resultExpr with
        | some v =>
          match v with
          | Value.num n => IO.println s!"Result: {n}"
          | Value.bool b => IO.println s!"Result: {b}"
          | Value.unit => IO.println s!"Result: unit"
          | Value.str s => IO.println (s!"Result: " ++ s)
          | Value.loc l => IO.println s!"Result: loc {l}"
          | Value.closure _ _ _ => IO.println s!"Result: <closure>"
          | Value.peClosure _ _ _ => IO.println s!"Result: <pure closure>"
          IO.println s!"Final state:"
          IO.println s!"  Variable environment: <function>"
          IO.println s!"  Memory: {repr config.memory}"
          return 0
        | none =>
          IO.println "Expression is not fully evaluated."
          IO.println s!"Remaining: {repr resultExpr}"
          IO.println s!"Final state:"
          IO.println s!"  Variable environment: <function>"
          IO.println s!"  Memory: {repr config.memory}"
          return 1

    catch e =>
      IO.println s!"Error reading file {filename}: {e}"
      return 1

  | ["--repl"] =>
    IO.println s!"Poison {versionNo} - Tufts University."
    IO.println "Type :quit to exit."
    IO.println "Enter a blank line after an expression to evaluate it."
    let tmp ← IO.Process.output { cmd := "mktemp", args := #["--tmpdir", "repl-XXXXXX.poison"] }
    let tmpPath := tmp.stdout.trim
    let initialConfig := ⟨ emptyMemory, emptyVarEnv,  0 ⟩
    replLoop initialConfig tmpPath

  | [filename] =>
    -- One argument: evaluate file
    runFile filename


  | _ =>
    -- Too many arguments: show usage
    IO.println "Usage:"
    IO.println "  poison-interpreter --repl          # Runs read-eval-print loop"
    IO.println "  poison-interpreter <file>           # Evaluate expressions from file"
    IO.println "  poison-interpreter --verbose <file> # Evaluate with step-by-step output"
    return 1
