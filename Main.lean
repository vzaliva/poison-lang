import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.Eval
import LeanPoison.Parser
import Lean.Data.Xml.Parser
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
  | [filename] =>
    -- One argument: evaluate file
    runFile filename
  | _ =>
    -- Too many arguments: show usage
    IO.println "Usage:"
    IO.println "  poison-interpreter <file>           # Evaluate expressions from file"
    IO.println "  poison-interpreter --verbose <file> # Evaluate with step-by-step output"
