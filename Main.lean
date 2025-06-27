import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.Eval
import LeanPoison.Parser

def evalProgram (input : String) : IO Unit := do
  match parseString input with
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
    IO.println s!"Parse error: {err}"

-- Read and evaluate a file
def runFile (filename : String) : IO Unit := do
  try
    let contents ← IO.FS.readFile filename
    IO.println s!"Evaluating file: {filename}"
    IO.println ""
    evalProgram contents
  catch e =>
    IO.println s!"Error reading file {filename}: {e}"

def main (args : List String) : IO Unit := do
  match args with
  | ["--verbose", filename] =>
    -- Verbose mode: evaluate file with step-by-step output
    try
      let contents ← IO.FS.readFile filename
      IO.println s!"Evaluating file: {filename} (verbose mode)"
      IO.println ""
      match parseString contents with
      | Except.ok expr =>
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
      | Except.error err =>
        IO.println s!"Parse error: {err}"
    catch e =>
      IO.println s!"Error reading file {filename}: {e}"
  | [filename] =>
    -- One argument: evaluate file
    runFile filename
  | [] =>
    -- No arguments: run a test case
    IO.println "Running closure test..."
    let testExpr := Expr.let "f" (Typ.arrow Typ.int Typ.int)
      (Expr.fn "x" Typ.int (Expr.op (Expr.var "x") Op.add (Expr.num 1)))
      (Expr.app (Expr.var "f") (Expr.num 5))
    let (config, resultExpr) :=run defaultFuel testExpr
    match Expr.toValue? resultExpr with
    | some v =>
      match v with
      | Value.num n => IO.println s!"Closure test result: {n}"
      | _ => IO.println s!"Closure test result: {v}"
    | none =>
      IO.println s!"Closure test not fully evaluated: {repr resultExpr}"
    IO.println s!"Final state:"
    IO.println s!"  Variable environment: <function>"
    IO.println s!"  Memory: {config.memory.toList}"
  | _ =>
    -- No arguments or too many: show usage
    IO.println "Usage:"
    IO.println "  poison-interpreter <file>           # Evaluate expressions from file"
    IO.println "  poison-interpreter --verbose <file> # Evaluate with step-by-step output"
