import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanPoison.Parser
import LeanPoison.Typecheck
import LeanPoison.Xml.Parser
import Init.System.IO
import Lean
import Std.Data.ExtTreeMap
open Std
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

-- Default fuel amount for evaluation and typechecking
def defaultFuel : Nat := 1000
-- Language Version No
def versionNo := "1.0"

-- ----------------------------------------------------------------------------
-- Built-in extern implementations.
-- The interpreter ships with a fixed, publicly documented set of externs that
-- unit tests may invoke by their well-known identifiers:
--   @10 : outer pure-fn stage of curried `max` (int -> ...)
--   @11 : inner pure-fn stage of curried `max`, expects captured `a` in env
--   @12 : pure `abs` (int -> int)
--   @20 : extern val ZERO  : int         (constant 0)
--   @21 : extern val errno : ref int     (driver-allocated cell, init 0)
--   @22 : extern fn  set_err n : (int) -> unit   (writes n into !errno)
-- See `doc/ffi-proposal.md` and `doc/poison-lang-description.tex`.
-- ----------------------------------------------------------------------------

/-- Driver-chosen runtime address for the `errno` cell (`@21`). Placed high
    so the driver-supplied cell is visually distinct from program-allocated
    ones in test goldens; `Config.nextAddr` still starts at `0`. -/
private def errnoAddr : Address := 1000000

private def outerMaxImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | unifiedEnv, Value.num _a, _m =>
      let innerRet  : ExternReturn := .simple .int false .noPred
      -- Inner `@11` argument condition must match the source declaration of
      -- curried `max`'s inner stage: `(int :> clean {})` (honest clean precondition).
      let innerNode : _root_.Expr := .externPfn 11 "b" .int false .noPred innerRet []
      .ok (Value.peClosure "b" innerNode unifiedEnv)
  | _, _, _ => .error (.implFailure 10 "expected int argument")

private def innerMaxImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | unifiedEnv, Value.num b, _m =>
      match VarEnv.lookup unifiedEnv "a" with
      | some (Value.num a) => .ok (Value.num (max a b))
      | _ => .error (.implFailure 11 "captured `a` missing or not an int")
  | _, _, _ => .error (.implFailure 11 "expected int argument")

private def absImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | _, Value.num n, _ => .ok (Value.num (Int.ofNat n.natAbs))
  | _, _, _           => .error (.implFailure 12 "expected int argument")

/-- Integer square root.  Used by the `sqrt`-style extern argument-condition
    example (`examples/extern_arg_precond_sqrt.poison`): its honest clean output
    relies on the caller-side precondition `x >= 0`, not on a runtime branch. -/
private def sqrtImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | _, Value.num n, _ => .ok (Value.num (Int.ofNat (Nat.sqrt n.toNat)))
  | _, _, _           => .error (.implFailure 19 "expected int argument")

/-- `set_err n` writes `n` into the `errno` cell and returns `unit`. No new
    allocation, so `nextAddr` is threaded through unchanged. -/
private def setErrImpl
    : VarEnv → Value → Memory → Address →
      Except ExternError (Value × Memory × Address)
  | _, Value.num n, mem, next =>
      .ok (Value.unit, Memory.update mem errnoAddr n, next)
  | _, _, _, _ => .error (.implFailure 22 "expected int argument")

/-- Bundled initial runtime state shipped with the interpreter: the registry,
    pre-populated memory (the `errno` cell), and `nextAddr` (unchanged at `0`
    since `errnoAddr` sits above the program-visible allocation range). -/
structure DefaultInitialState where
  memory   : Memory
  nextAddr : Address
  registry : ExternRegistry

/-- Registry/insert helper. `register` failures are impossible here because
    all ids are hard-coded literals; `panic!` is purely defensive. -/
private def regInsert (reg : ExternRegistry) (id : ExternId) (impl : ExternImpl)
    : ExternRegistry :=
  match register reg id impl with
  | .ok r => r
  | .error e => panic! s!"defaultInitialState: {e}"

/-- Build the default registry and driver-supplied initial memory/cursor. -/
def defaultInitialState : DefaultInitialState :=
  let mem0 : Memory := Memory.update emptyMemory errnoAddr 0
  let r0 : ExternRegistry := ∅
  let r1 := regInsert r0 10 (.pfn outerMaxImpl)
  let r2 := regInsert r1 11 (.pfn innerMaxImpl)
  let r3 := regInsert r2 12 (.pfn absImpl)
  let r4 := regInsert r3 20 (.val (Value.num 0))
  let r5 := regInsert r4 21 (.val (Value.loc errnoAddr))
  let r6 := regInsert r5 22 (.fn setErrImpl)
  let r7 := regInsert r6 19 (.pfn sqrtImpl)
  { memory := mem0, nextAddr := 0, registry := r7 }

/-- Back-compat alias: older call sites that just want the registry. -/
def defaultRegistry : ExternRegistry := defaultInitialState.registry

private def initialTypeContext (regime : Regime)
    (externRegime : ExternId → Tag → Option Bool := fun _ _ => none) : TypeContext :=
  {
    pc := false
    regime := regime
    externRegime := externRegime
    memEnv := {}
    varEnv := ({} : VarTypeEnv)
    tagEnv := {}
    nextLoc := 0
    nextTag := 1
    pureCtx := false
  }

def typecheckExprSimple (e : _root_.Expr) (regime : Regime := emptyRegime)
    (externRegime : ExternId → Tag → Option Bool := fun _ _ => none) : TypecheckM QTyp := do
  let result ← typecheck (initialTypeContext regime externRegime) e defaultFuel
  return result.qualType

def typecheckExprVerbose (e : _root_.Expr) (regime : Regime := emptyRegime)
    (externRegime : ExternId → Tag → Option Bool := fun _ _ => none) : TypecheckM TypeResult := do
  typecheck (initialTypeContext regime externRegime) e defaultFuel

structure CliOptions where
  verbose : Bool := false
  regime : Option Regime := none
  externRegime : ExternId → Tag → Option Bool := fun _ _ => none
  filename : Option String := none
  repl : Bool := false
  help : Bool := false

private def stringDoc (s : String) : Std.Format :=
  Std.Format.joinSep (s.splitOn "\n") Std.Format.line

private def printDoc (doc : Std.Format) : IO Unit :=
  IO.println (Std.Format.pretty doc)

private def formatTypecheckPassedSimple (qualType : QTyp) : Std.Format :=
  Std.Format.group (
    Std.Format.text "Type checking passed:" ++
    Std.Format.nest 2 (
      Std.Format.line ++
      Std.Format.text "Type: " ++
      repr qualType
    )
  )

private def formatTypecheckPassedVerbose (result : TypeResult) : Std.Format :=
  Std.Format.group (
    Std.Format.text "Type checking passed:" ++
    Std.Format.nest 2 (
      Std.Format.line ++ Std.Format.text "Type: " ++ repr result.qualType ++ Std.Format.text "," ++
      Std.Format.line ++ Std.Format.text "MemoryTypeEnv: " ++ repr result.memEnv' ++ Std.Format.text "," ++
      Std.Format.line ++ Std.Format.text "tagEnv: " ++ repr result.tagEnv' ++ Std.Format.text "," ++
      Std.Format.line ++ Std.Format.text "nextLoc: " ++ repr result.nextLoc'
    )
  )

private def formatTypecheckError (msg : String) : Std.Format :=
  Std.Format.group (
    Std.Format.text "Type checking error:" ++
    Std.Format.nest 2 (Std.Format.line ++ stringDoc msg)
  )

def parseRegimeSpec (spec : String) : Except String Regime := do
  let parts := spec.splitOn ","
  let mut map : ExtTreeMap Nat Bool := {}
  let mut hasEntry := false
  for entry in parts do
    let trimmed := entry.trimAscii.toString
    if trimmed.isEmpty then
      throw "Invalid --regime entry: empty assignment"
    let kv := trimmed.splitOn "="
    match kv with
    | [tagStr, valStr] =>
        let tagStr := tagStr.trimAscii.toString
        let valStr := valStr.trimAscii.toString
        let tagOpt := tagStr.toNat?
        match tagOpt with
        | none => throw s!"Invalid --regime tag: {tagStr}"
        | some tag =>
            let boolOpt :=
              if valStr == "true" then some true
              else if valStr == "false" then some false
              else none
            match boolOpt with
            | none => throw s!"Invalid --regime value for tag {tag}: {valStr}"
            | some b =>
                map := map.insert tag b
                hasEntry := true
    | _ => throw s!"Invalid --regime assignment: {trimmed}"
  if not hasEntry then
    throw "Invalid --regime: no assignments provided"
  return map

/-- Parse `--extern-regime "238=true,239=false"` into an id-only executable policy:
    every output tag generated for an extern id receives the same boolean. -/
def parseExternRegimeSpec (spec : String) :
    Except String (ExternId → Tag → Option Bool) := do
  let parts := spec.splitOn ","
  let mut map : ExtTreeMap ExternId Bool := {}
  let mut hasEntry := false
  for entry in parts do
    let trimmed := entry.trimAscii.toString
    if trimmed.isEmpty then
      throw "Invalid --extern-regime entry: empty assignment"
    let kv := trimmed.splitOn "="
    match kv with
    | [idStr, valStr] =>
        let idStr := idStr.trimAscii.toString
        let valStr := valStr.trimAscii.toString
        match idStr.toNat? with
        | none => throw s!"Invalid --extern-regime id: {idStr}"
        | some id =>
            let boolOpt :=
              if valStr == "true" then some true
              else if valStr == "false" then some false
              else none
            match boolOpt with
            | none => throw s!"Invalid --extern-regime value for id {id}: {valStr}"
            | some b =>
                map := map.insert id b
                hasEntry := true
    | _ => throw s!"Invalid --extern-regime assignment: {trimmed}"
  if not hasEntry then
    throw "Invalid --extern-regime: no assignments provided"
  return fun id _tag => map[id]?

partial def parseArgs (args : List String) (opts : CliOptions := {}) : Except String CliOptions :=
  match args with
  | [] => return opts
  | "--verbose" :: rest =>
      parseArgs rest { opts with verbose := true }
  | "--regime" :: spec :: rest =>
      match parseRegimeSpec spec with
      | .ok reg => parseArgs rest { opts with regime := some reg }
      | .error msg => throw msg
  | "--regime" :: [] =>
      throw "Missing value for --regime"
  | "--extern-regime" :: spec :: rest =>
      match parseExternRegimeSpec spec with
      | .ok policy => parseArgs rest { opts with externRegime := policy }
      | .error msg => throw msg
  | "--extern-regime" :: [] =>
      throw "Missing value for --extern-regime"
  | "--repl" :: rest =>
      if rest.isEmpty then
        return { opts with repl := true }
      else
        throw "Unexpected arguments after --repl"
  | "--help" :: rest =>
      if rest.isEmpty then
        return { opts with help := true }
      else
        throw "Unexpected arguments after --help"
  | arg :: rest =>
      if arg.startsWith "-" then
        throw s!"Unknown option: {arg}"
      else
        match opts.filename with
        | some _ => throw "Multiple input files provided"
        | none => parseArgs rest { opts with filename := some arg }

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

def evalProgram (input : String) (verbose : Bool) (regime : Regime)
    (externRegime : ExternId → Tag → Option Bool := fun _ _ => none) : IO UInt32 := do
  match parse input with
  | Except.ok xmlElement =>

    match xmlToExpr xmlElement with
    | Except.ok expr =>
      if verbose then
        match typecheckExprVerbose expr regime externRegime with
        | .ok resultType =>
            printDoc (formatTypecheckPassedVerbose resultType)
            let st := defaultInitialState
            let initialConfig : Config := ⟨st.memory, emptyVarEnv, st.nextAddr, false, st.registry⟩
            let result := LeanPoison.beval defaultFuel initialConfig expr verbose
            handleEvalResult result verbose
        | .error errorMsg =>
            printDoc (formatTypecheckError errorMsg)
            if errorMsg.trimAscii.toString == "Out of fuel" then
              return (4 : UInt32)  -- Exit code 4: Type checker out of fuel
            else
              return (0 : UInt32)  -- Exit code 0: Type error successfully found
      else
        match typecheckExprSimple expr regime externRegime with
        | .ok qualType =>
            printDoc (formatTypecheckPassedSimple qualType)
            let st := defaultInitialState
            let initialConfig : Config := ⟨st.memory, emptyVarEnv, st.nextAddr, false, st.registry⟩
            let result := LeanPoison.beval defaultFuel initialConfig expr verbose
            handleEvalResult result verbose
        | .error errorMsg =>
            printDoc (formatTypecheckError errorMsg)
            if errorMsg.trimAscii.toString == "Out of fuel" then
              return (4 : UInt32)
            else
              return (0 : UInt32)

    | Except.error err =>
      IO.println s!"Error while building expression tree: {err}"
      return (3 : UInt32)  -- Exit code 3: AST construction error

  | Except.error e => IO.println s!"Parse error: {e}"
                      return (2 : UInt32)  -- Exit code 2: Parse error

-- Read and evaluate a file
def runFile (filename : String) (verbose : Bool) (regime : Regime)
    (externRegime : ExternId → Tag → Option Bool := fun _ _ => none) : IO UInt32 := do
  try
    let xmlStr ← runTreeSitterXml filename
    IO.println s!"Evaluating file: {filename}"
    IO.println ""
    evalProgram xmlStr verbose regime externRegime
  catch e =>
    IO.println s!"Error reading file {filename}: {e}"
    return (5 : UInt32)  -- Exit code 5: File I/O error
-------------------------------------------------------------------------------
partial def readMultiline (acc : String := "") : IO String := do
  IO.print " > "
  let unline ← IO.getStdin
  let line <- unline.getLine
  let newAcc := acc ++ "\n" ++ line
  if line.trimAscii.toString.isEmpty then
    return newAcc.trimAscii.toString
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
      -- Run the same typechecker as the file path: this enforces extern
      -- identifier uniqueness, first-order-input rules, and reports any type
      -- error visibly to the user before evaluation.
      match typecheckExprSimple expr with
      | .error msg =>
          IO.println s!"Type checking error: {msg}"
          IO.FS.removeFile tmpPath
          replLoop config tmpPath
      | .ok _ =>
        -- Evaluate using the REPL's persistent config (seeded with
        -- `defaultRegistry`) so built-in externs are available.
        match LeanPoison.beval defaultFuel config expr false with
        | .success newConfig v =>
          IO.println s!"Result: {v}"
          IO.println s!"Memory: {newConfig.memory}"
          IO.FS.removeFile tmpPath
          replLoop newConfig tmpPath
        | .outOfFuel =>
          IO.println "Error: out of fuel (program may diverge)"
          IO.FS.removeFile tmpPath
          replLoop config tmpPath
        | .runtimeError msg =>
          IO.println s!"Runtime error: {msg}"
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
  IO.println "  poison-interpreter [--verbose] [--regime \"100=true,101=false\"] [--extern-regime \"238=true\"] <file>"
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
  match parseArgs args with
  | .error msg =>
      IO.println s!"Error: {msg}"
      printUsage
      return (1 : UInt32)
  | .ok opts =>
      if opts.help then
        printUsage
        return (0 : UInt32)
      else if opts.repl then
        if opts.filename.isSome || opts.regime.isSome || opts.verbose then
          IO.println "Error: --repl does not accept --verbose, --regime, or a filename"
          printUsage
          return (1 : UInt32)
        IO.println s!"Poison {versionNo} - Tufts University."
        IO.println "Type :quit to exit."
        IO.println "Enter a blank line after an expression to evaluate it."
        let tmp ← IO.Process.output { cmd := "mktemp", args := #["--tmpdir", "repl-XXXXXX.poison"] }
        let tmpPath := tmp.stdout.trimAscii.toString
        let st := defaultInitialState
        let initialConfig := ⟨ st.memory, emptyVarEnv, st.nextAddr, false, st.registry ⟩
        replLoop initialConfig tmpPath
      else
        let regime := opts.regime.getD emptyRegime
        let externRegime := opts.externRegime
        match opts.filename with
        | none =>
            IO.println "Error: missing input file"
            printUsage
            return (1 : UInt32)
        | some filename =>
            if opts.verbose then
              try
                let ExprTree ← parsePoisonFile filename
                IO.println s!"Evaluating file: {filename} (verbose mode)"
                IO.println ""
                match ExprTree with
                | expr =>
                  match typecheckExprVerbose expr regime externRegime with
                  | .ok resultType =>
                      printDoc (formatTypecheckPassedVerbose resultType)
                      IO.println ""
                      let st := defaultInitialState
                      let initialConfig : Config := ⟨st.memory, emptyVarEnv, st.nextAddr, false, st.registry⟩
                      let result := LeanPoison.beval defaultFuel initialConfig expr true
                      handleEvalResult result true
                  | .error errorMsg =>
                      printDoc (formatTypecheckError errorMsg)
                      IO.println ""
                      if errorMsg.trimAscii.toString == "Out of fuel" then
                        return (4 : UInt32)
                      else
                        return (0 : UInt32)
              catch e =>
                IO.println s!"Error reading file {filename}: {e}"
                return (5 : UInt32)
            else
              runFile filename false regime externRegime
