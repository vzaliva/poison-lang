/- Big-step interpreter for LeanPoison (mirrors Ott big-step rules)
   Uses Except for errors; no dependency on SmallStep.StepResult. -/

import LeanPoison.Syntax
import LeanPoison.Runtime
import Std.Data.HashMap
import Mathlib.Data.Int.Bitwise
open Std

namespace LeanPoison

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
      Returns Either error or final (Config × Value). -/
  def beval (fuel : Nat) (config : Config) (expr : Expr) (verbose : Bool) : IO (Except String (Config × Value)) := do
    let _ := bsTraceEnter fuel verbose config expr
    if fuel = 0 then
      return .error "out of fuel"
    else
      match expr with
      -- Literals
      | Expr.num n =>
        return .ok (config, Value.num n)
      | Expr.bool b =>
        return .ok (config, Value.bool b)
      | Expr.unit =>
        return .ok (config, Value.unit)
      | Expr.str s =>
        return .ok (config, Value.str s)

      -- Variables
      | Expr.var x =>
        match config.varEnv.lookup x with
        | some v => return .ok (config, v)
        | none   => return .error s!"var {x} not found"

      -- Binary operations (evaluate operands then compute)
      | Expr.op e1 op e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .ok (config', v1) =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .ok (config'', v2) =>
            match evalOp op v1 v2 with
            | some v => return .ok (config'', v)
            | none =>
              let v1Str := ValueToTypeString v1
              let v2Str := ValueToTypeString v2
              let opStr := toString op
              return .error s!"Runtime type error: cannot apply operation {opStr} to {v1Str} and {v2Str}"
          | .error msg => return .error msg
        | .error msg => return .error msg

      -- Unary operations
      | Expr.unaryop op e => do
        match <- beval (fuel - 1) config e verbose with
         | .ok (config', v) =>
            match evalUnaryOp op v with
            | some v' => return .ok (config', v')
            | none =>
              let vStr := ValueToTypeString v
              let opStr := toString op
              return .error s!"Runtime type error: cannot apply operation {opStr} to {vStr}"
         | .error msg => return .error msg


      -- References
      | Expr.newRef e => do
        match <- beval (fuel - 1) config e verbose with
        | .ok (config', Value.num n) =>
          let (l, config'') := freshLoc config'
          let config''' := { config'' with memory := config''.memory.update l n }
          return .ok (config''', Value.loc l)
        | .ok _ => return .error "Runtime type error: ref expects a number"
        | .error msg => return .error msg

      -- Dereference
      | Expr.deref e => do
        match <- beval (fuel - 1) config e verbose with
        | .ok (config', Value.loc l) =>
          match config'.memory.get? l with
          | some n => return .ok (config', Value.num n)
          | none   => return .error s!"Runtime type error: deref uninitialized location {l}"
        | .ok (_, v) => return .error s!"Runtime type error: deref expects a location but got {v}"
        | .error msg => return .error msg

      -- Assignment
      | Expr.assign e1 e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .ok (config', Value.loc l) =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .ok (config'', Value.num n) =>
            let config''' := { config'' with memory := config''.memory.update l n }
            return .ok (config''', Value.unit)
          | .ok _ => return .error "Runtime type error: assignment expects number on right side"
          | .error msg => return .error msg
        | .ok _ => return .error "Runtime type error: assignment expects location on left side"
        | .error msg => return .error msg

      -- Sequencing
      | Expr.seq e1 e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .ok (config', _v1) =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .ok (config'', v2) => return .ok (config'', v2)
          | .error msg => return .error msg
        | .error msg => return .error msg

      -- Conditionals
      | Expr.ite e1 e2 e3 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .ok (config', Value.bool true) =>
          match <- beval (fuel - 1) config' e2 verbose with
          | .ok (config'', v) => return .ok (config'', v)
          | .error msg => return .error msg
        | .ok (config', Value.bool false) =>
          match <- beval (fuel - 1) config' e3 verbose with
          | .ok (config'', v) => return .ok (config'', v)
          | .error msg => return .error msg
        | .ok _ => return .error "Runtime type error: condition must be boolean"
        | .error msg => return .error msg

      -- While (via if-expansion to mirror small-step rule)
      | Expr.kwhile e1 e2 =>
        let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.kwhile e1 e2)) Expr.unit
        beval (fuel - 1) config unfolded verbose

      -- Let binding
      | Expr.vlet x e1 e2 => do
        match <- beval (fuel - 1) config e1 verbose with
        | .ok (config', v) =>
          let config'' := { config' with varEnv := config'.varEnv.update x v }
          match <- beval (fuel - 1) config'' e2 verbose with
          | .ok (config''', v2) =>
            -- Restore original variable environment, keeping memory changes
            -- According to OTT semantics, let-bound variables should not escape their scope
            let finalConfig := { config''' with varEnv := config'.varEnv }
            return .ok (finalConfig, v2)
          | .error msg => return .error msg
        | .error msg => return .error msg

      -- Function abstractions
      | Expr.fn x _ body _ =>
        let closure := Value.closure x body config.varEnv
        return .ok (config, closure)
      | Expr.pfn x _ body _ =>
        let closure := Value.peClosure x body config.varEnv
        return .ok (config, closure)

      -- Application (call-by-value: evaluate argument first, then function)
      | Expr.app e1 e2 => do
        match <- beval (fuel - 1) config e2 verbose with
        | .ok (config', v2) =>
          match <- beval (fuel - 1) config' e1 verbose with
          | .ok (config'', Value.closure x body env) =>
            if config''.pureMode then
              return .error "Pure function cannot apply impure closure"
            else
              bevalFunctionBody (fuel - 1) verbose config'' env x v2 body false
          | .ok (config'', Value.peClosure x body env) =>
            bevalFunctionBody (fuel - 1) verbose config'' env x v2 body true
          | .ok _ => return .error "Runtime type error: expected function in application"
          | .error msg => return .error msg
        | .error msg => return .error msg

      -- Built-ins
      | Expr.rand e => do
        match <- beval (fuel - 1) config e verbose with
        | .ok (config', Value.num n) =>
          if n >= 0 then
            let r ← (IO.rand 0 n.toNat).toIO
            let randomNo := Int.ofNat r
            return .ok (config', Value.num randomNo)
          else
            IO.println "Argument to rand must evaluate to non negative integer"
            return .error "Argument to rand must evaluate to non negative integer"
        | .ok _ => return .error "Runtime type error: rand expects a number"
        | .error msg => return .error msg

      | Expr.frand e => do
        match <- beval (fuel - 1) config e verbose with
        | .ok (config', Value.num n) =>
          if n >= 0 then
            let maxRange : Nat := 4 * (n.toNat)
            let r ← (IO.rand 0 maxRange).toIO   -- 0 ≤ r ≤ 4n
            let randomNo : Int := (Int.ofNat r) - (2 * n)  -- -2n ≤ randomNo ≤ 2n
            return .ok (config', Value.num randomNo)
          else
            IO.println "Argument to frand must evaluate to non negative integer"
            return .error "Argument to frand must evaluate to non negative integer"
        | .ok _ => return .error "Runtime type error: frand expects a number"
        | .error msg => return .error msg

      | Expr.printInt e => do
        match <- beval (fuel - 1) config e verbose with
        | .ok (config', Value.num n) =>
          IO.println n
          return .ok (config', Value.unit)
        | .ok _ => return .error "printInt expects argument to evaluate to an integer."
        | .error msg => return .error msg

      | Expr.printString e => do
        match <- beval (fuel - 1) config e verbose with
        | .ok (config', Value.str s) =>
          IO.println s
          return .ok (config', Value.unit)
        | .ok _ => return .error "printString expects argument to evaluate to a string."
        | .error msg => return .error msg

  /-- Helper for evaluating function bodies (impure vs pure) -/
  def bevalFunctionBody (fuel : Nat) (verbose : Bool)
                        (currentConfig : Config) (closureEnv : VarEnv)
                        (paramName : Name) (argValue : Value) (body : Expr)
                        (isPure : Bool) : IO (Except String (Config × Value)) := do
    match fuel with
    | 0 => return .error "out of fuel in function evaluation"
    | fuel' + 1 =>
      let updatedEnv := VarEnv.update closureEnv paramName argValue
      let bodyConfig := { currentConfig with varEnv := updatedEnv, pureMode := isPure }
      match <- beval fuel' bodyConfig body verbose with
      | .ok (evalConfig, v) =>
        if isPure then
          return .ok ({ currentConfig with pureMode := false }, v)
        else
          let finalConfig := { currentConfig with memory := evalConfig.memory, nextLoc := evalConfig.nextLoc, pureMode := false }
          return .ok (finalConfig, v)
      | .error msg =>
        return .error msg

end -- mutual

/- Convenience runner similar to SmallStep.run -/
def runBig (fuel : Nat) (expr : Expr) (verbose : Bool := false) : IO (Config × ExprOrValue) := do
  let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0, false⟩
  match <- beval fuel initialConfig expr verbose with
  | .ok (config, v) => return (config, ExprOrValue.value v)
  | .error msg => do
    IO.println s!"Error: {msg}"
    return (initialConfig, ExprOrValue.expr expr)

end LeanPoison
