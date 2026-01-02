/- Big-step interpreter for LeanPoison (mirrors Ott big-step rules)
   Uses Except for errors; no dependency on SmallStep.StepResult. -/

import LeanPoison.Syntax
import LeanPoison.Runtime
import Mathlib.Data.Int.Bitwise
open Std

namespace LeanPoison

-- Result type for big-step evaluation to distinguish termination, divergence, and stuck states
inductive EvalResult : Type where
  | success : Config → Value → EvalResult      -- Termination: successful evaluation
  | outOfFuel : EvalResult                     -- Divergence: fuel exhausted
  | runtimeError : String → EvalResult         -- Stuck state: runtime error

-- Lightweight debug entry trace for big-step
def bsTraceEnter (fuel : Nat) (verbose : Bool) (_config : Config) (expr : Expr) : Unit :=
  if verbose then dbg_trace s!"→ BS [{fuel}]:\t⟨{repr expr}⟩"; () else ()

-- Operation evaluator (local copy to avoid depending on SmallStep)
def evalOp (op : Op) (v1 v2 : Value) : Option Value :=
  match op, v1, v2 with
  | Op.add, Value.num n1, Value.num n2 => some (Value.num (n1 + n2))
  | Op.sub, Value.num n1, Value.num n2 => some (Value.num (n1 - n2))
  | Op.mul, Value.num n1, Value.num n2 => some (Value.num (n1 * n2))
  | Op.div, Value.num n1, Value.num n2 => some (Value.num (n1 / n2))
  | Op.gte, Value.num n1, Value.num n2 => some (Value.bool (n1 >= n2))
  | Op.lte, Value.num n1, Value.num n2 => some (Value.bool (n1 <= n2))
  | Op.gt,  Value.num n1, Value.num n2 => some (Value.bool (n1 > n2))
  | Op.lt,  Value.num n1, Value.num n2 => some (Value.bool (n1 < n2))
  | Op.eq,  Value.num n1, Value.num n2 => some (Value.bool (n1 == n2))
  | Op.and, Value.bool b1, Value.bool b2 => some (Value.bool (b1 && b2))
  | Op.or,  Value.bool b1, Value.bool b2 => some (Value.bool (b1 || b2))
  | Op.neq, Value.num n1, Value.num n2 => some (Value.bool (n1 != n2))
  | Op.bitand, Value.num n1, Value.num n2 => some (Value.num (Int.land n1 n2))
  | _, _, _ => none

def evalUnaryOp (op : UnaryOp) (v : Value) : Option Value :=
  match op, v  with
  | UnaryOp.not, Value.bool b => some (Value.bool (!b))
  | _, _ => none
mutual

  /-- Big-step evaluation: evaluates an expression to a value using fuel.
      Returns EvalResult distinguishing success, divergence, and runtime errors. -/
  def beval (fuel : Nat) (config : Config) (expr : Expr) (verbose : Bool) : IO EvalResult := do
    let _ := bsTraceEnter fuel verbose config expr
    if fuel = 0 then
      return .outOfFuel
    else
      match expr with
      -- Literals
      | Expr.num n =>
        return .success config (Value.num n)
      | Expr.bool b =>
        return .success config (Value.bool b)
      | Expr.unit =>
        return .success config Value.unit
      | Expr.str s =>
        return .success config (Value.str s)

      -- Variables
      | Expr.var x =>
        match config.varEnv.lookup x with
        | some v => return .success config v
        | none   => return .runtimeError s!"var {x} not found"

      -- Binary operations (evaluate operands then compute)
      | Expr.op e1 op e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .success config' v1 =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .success config'' v2 =>
            match evalOp op v1 v2 with
            | some v => return .success config'' v
            | none =>
              let v1Str := ValueToTypeString v1
              let v2Str := ValueToTypeString v2
              let opStr := toString op
              return .runtimeError s!"Runtime type error: cannot apply operation {opStr} to {v1Str} and {v2Str}"
          | .outOfFuel => return .outOfFuel
          | .runtimeError msg => return .runtimeError msg
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- Unary operations
      | Expr.unaryop op e => do
        match <- beval (fuel - 1) config e verbose with
         | .success config' v =>
            match evalUnaryOp op v with
            | some v' => return .success config' v'
            | none =>
              let vStr := ValueToTypeString v
              let opStr := toString op
              return .runtimeError s!"Runtime type error: cannot apply operation {opStr} to {vStr}"
         | .outOfFuel => return .outOfFuel
         | .runtimeError msg => return .runtimeError msg


      -- References
      | Expr.newRef e => do
        match <- beval (fuel - 1) config e verbose with
        | .success config' (Value.num n) =>
          let (l, config'') := freshAddr config'
          let config''' := { config'' with memory := config''.memory.update l n }
          return .success config''' (Value.loc l)
        | .success _ _ => return .runtimeError "Runtime type error: ref expects a number"
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- Dereference
      | Expr.deref e => do
        match <- beval (fuel - 1) config e verbose with
        | .success config' (Value.loc l) =>
          match config'.memory.get? l with
          | some n => return .success config' (Value.num n)
          | none   => return .runtimeError s!"Runtime type error: deref uninitialized location {l}"
        | .success _ v => return .runtimeError s!"Runtime type error: deref expects a location but got {v}"
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- Assignment
      | Expr.assign e1 e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .success config' (Value.loc l) =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .success config'' (Value.num n) =>
            let config''' := { config'' with memory := config''.memory.update l n }
            return .success config''' Value.unit
          | .success _ _ => return .runtimeError "Runtime type error: assignment expects number on right side"
          | .outOfFuel => return .outOfFuel
          | .runtimeError msg => return .runtimeError msg
        | .success _ _ => return .runtimeError "Runtime type error: assignment expects location on left side"
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- Sequencing
      | Expr.seq e1 e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .success config' _v1 =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .success config'' v2 => return .success config'' v2
          | .outOfFuel => return .outOfFuel
          | .runtimeError msg => return .runtimeError msg
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- Conditionals
      | Expr.ite e1 e2 e3 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .success config' (Value.bool true) =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .success config'' v => return .success config'' v
          | .outOfFuel => return .outOfFuel
          | .runtimeError msg => return .runtimeError msg
        | .success config' (Value.bool false) =>
          match <- beval (fuel - 1) config' e3 verbose with
          | .success config'' v => return .success config'' v
          | .outOfFuel => return .outOfFuel
          | .runtimeError msg => return .runtimeError msg
        | .success _ _ => return .runtimeError "Runtime type error: condition must be boolean"
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- While (via if-expansion to mirror small-step rule)
      | Expr.kwhile e1 e2 =>
        let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
        beval (fuel - 1) config unfolded verbose

      -- Let binding
      | Expr.vlet x e1 e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .success config' v =>
          let config'' := { config' with varEnv := config'.varEnv.update x v }
          match <- beval (fuel - 1) config'' e2 verbose with
          | .success config''' v2 =>
            -- Restore original variable environment, keeping memory changes
            -- According to OTT semantics, let-bound variables should not escape their scope
            let finalConfig := { config''' with varEnv := config'.varEnv }
            return .success finalConfig v2
          | .outOfFuel => return .outOfFuel
          | .runtimeError msg => return .runtimeError msg
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- Function abstractions
      | Expr.fn x _ body _ =>
        let closure := Value.closure x body config.varEnv
        return .success config closure
      | Expr.pfn x _ body _ =>
        let closure := Value.peClosure x body config.varEnv
        return .success config closure

      -- Application (call-by-value: evaluate argument first, then function)
      | Expr.app e1 e2 => do
        match <- beval (fuel - 1) config e2 verbose with
        | .success config' v2 =>
          match <- beval (fuel - 1) config' e1 verbose with
          | .success config'' (Value.closure x body env) =>
            if config''.pureMode then
              return .runtimeError "Pure function cannot apply impure closure"
            else
              bevalFunctionBody (fuel - 1) verbose config'' env x v2 body false
          | .success config'' (Value.peClosure x body env) =>
            match Expr.toPExpr? body with
            | some _ => bevalFunctionBody (fuel - 1) verbose config'' env x v2 body true
            | none => return .runtimeError "Pure closure body is not pure"
          | .success _ _ => return .runtimeError "Runtime type error: expected function in application"
          | .outOfFuel => return .outOfFuel
          | .runtimeError msg => return .runtimeError msg
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      -- Extern placeholders (cannot be executed)
      | Expr.externVal _ _ _ =>
        return .runtimeError "Cannot execute extern value – no implementation provided"
      | Expr.externFn _ _ _ _ =>
        return .runtimeError "Cannot execute extern function – no implementation provided"
      | Expr.externPfn _ _ _ =>
        return .runtimeError "Cannot execute extern pure function – no implementation provided"

      -- Built-ins
      | Expr.rand e => do
        match <- beval (fuel - 1) config e verbose with
        | .success config' (Value.num n) =>
          if n >= 0 then
            let r ← (IO.rand 0 n.toNat).toIO
            let randomNo := Int.ofNat r
            return .success config' (Value.num randomNo)
          else
            IO.println "Argument to rand must evaluate to non negative integer"
            return .runtimeError "Argument to rand must evaluate to non negative integer"
        | .success _ _ => return .runtimeError "Runtime type error: rand expects a number"
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      | Expr.frand e => do
        match <- beval (fuel - 1) config e verbose with
        | .success config' (Value.num n) =>
          if n >= 0 then
            let maxRange : Nat := 4 * (n.toNat)
            let r ← (IO.rand 0 maxRange).toIO   -- 0 ≤ r ≤ 4n
            let randomNo : Int := (Int.ofNat r) - (2 * n)  -- -2n ≤ randomNo ≤ 2n
            return .success config' (Value.num randomNo)
          else
            IO.println "Argument to frand must evaluate to non negative integer"
            return .runtimeError "Argument to frand must evaluate to non negative integer"
        | .success _ _ => return .runtimeError "Runtime type error: frand expects a number"
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      | Expr.printInt e => do
        match <- beval (fuel - 1) config e verbose with
        | .success config' (Value.num n) =>
          IO.println n
          return .success config' Value.unit
        | .success _ _ => return .runtimeError "printInt expects argument to evaluate to an integer."
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

      | Expr.printString e => do
        match <- beval (fuel - 1) config e verbose with
        | .success config' (Value.str s) =>
          IO.println s
          return .success config' Value.unit
        | .success _ _ => return .runtimeError "printString expects argument to evaluate to a string."
        | .outOfFuel => return .outOfFuel
        | .runtimeError msg => return .runtimeError msg

  /-- Helper for evaluating function bodies (impure vs pure) -/
  def bevalFunctionBody (fuel : Nat) (verbose : Bool)
                        (currentConfig : Config) (closureEnv : VarEnv)
                        (paramName : Name) (argValue : Value) (body : Expr)
                        (isPure : Bool) : IO EvalResult := do
    match fuel with
    | 0 => return .outOfFuel
    | fuel' + 1 =>
      let updatedEnv := VarEnv.update closureEnv paramName argValue
      let bodyConfig := { currentConfig with varEnv := updatedEnv, pureMode := isPure }
      match <- beval fuel' bodyConfig body verbose with
      | .success evalConfig v =>
        if isPure then
          return .success ({ currentConfig with pureMode := false }) v
        else
          let finalConfig := { currentConfig with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := false }
          return .success finalConfig v
      | .outOfFuel => return .outOfFuel
      | .runtimeError msg => return .runtimeError msg

end -- mutual

/- Convenience runner that prints errors and returns EvalResult -/
def runBig (fuel : Nat) (expr : Expr) (verbose : Bool := false) : IO EvalResult := do
  let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0, false⟩
  let result <- beval fuel initialConfig expr verbose
  match result with
  | .outOfFuel => IO.println "Error: out of fuel"
  | .runtimeError msg => IO.println s!"Error: {msg}"
  | .success _ _ => pure ()
  return result

end LeanPoison
