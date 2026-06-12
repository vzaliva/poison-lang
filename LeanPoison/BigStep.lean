/- Big-step interpreter for LeanPoison (mirrors Ott big-step rules)
   Uses Except for errors; no dependency on SmallStep.StepResult. -/

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.Pretty
import Mathlib.Data.Int.Bitwise
open Std

namespace LeanPoison

-- Result type for big-step evaluation to distinguish termination, divergence, and stuck states
inductive EvalResult : Type where
  | success : Config → Value → EvalResult      -- Termination: successful evaluation
  | outOfFuel : EvalResult                     -- Divergence: fuel exhausted
  | runtimeError : String → EvalResult         -- Stuck state: runtime error

-- Lightweight debug entry trace for big-step
private def bsTraceEnter (fuel : Nat) (verbose : Bool) (_config : Config) (expr : Expr) : Unit :=
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
  def beval (fuel : Nat) (config : Config) (expr : Expr) (verbose : Bool) : EvalResult :=
    let _ := bsTraceEnter fuel verbose config expr
    if fuel = 0 then
      .outOfFuel
    else
      match expr with
      -- Literals
      | Expr.num n =>
        .success config (Value.num n)
      | Expr.bool b =>
        .success config (Value.bool b)
      | Expr.unit =>
        .success config Value.unit
      | Expr.str s =>
        .success config (Value.str s)

      -- Variables
      | Expr.var x =>
        match config.varEnv.lookup x with
        | some v => .success config v
        | none   => .runtimeError s!"var {x} not found"

      -- Binary operations (evaluate operands then compute)
      | Expr.op e1 op e2 =>
        match beval (fuel - 1) config e1 verbose with
        | .success config' v1 =>
          match beval (fuel - 1) config' e2 verbose with
          | .success config'' v2 =>
            match evalOp op v1 v2 with
            | some v => .success config'' v
            | none =>
              let v1Str := ValueToTypeString v1
              let v2Str := ValueToTypeString v2
              let opStr := toString op
              .runtimeError s!"Runtime type error: cannot apply operation {opStr} to {v1Str} and {v2Str}"
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg
        | .outOfFuel => .outOfFuel
        | .runtimeError msg => .runtimeError msg

      -- Unary operations
      | Expr.unaryop op e =>
        match beval (fuel - 1) config e verbose with
         | .success config' v =>
            match evalUnaryOp op v with
            | some v' => .success config' v'
            | none =>
              let vStr := ValueToTypeString v
              let opStr := toString op
              .runtimeError s!"Runtime type error: cannot apply operation {opStr} to {vStr}"
         | .outOfFuel => .outOfFuel
         | .runtimeError msg => .runtimeError msg


      -- References
      -- Pure-mode guard is defense-in-depth: typecheckPfn already rejects this
      -- syntactically via Expr.toPExpr at pfn definition (see Typecheck.lean).
      | Expr.newRef e =>
        if config.pureMode then
          .runtimeError "ref allocation forbidden in pure mode"
        else
          match beval (fuel - 1) config e verbose with
          | .success config' (Value.num n) =>
            let (l, config'') := freshAddr config'
            let config''' := { config'' with memory := config''.memory.update l n }
            .success config''' (Value.loc l)
          | .success _ _ => .runtimeError "Runtime type error: ref expects a number"
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg

      -- Dereference
      | Expr.deref e =>
        match beval (fuel - 1) config e verbose with
        | .success config' (Value.loc l) =>
          match config'.memory.get? l with
          | some n => .success config' (Value.num n)
          | none   => .runtimeError s!"Runtime type error: deref uninitialized location {l}"
        | .success _ v => .runtimeError s!"Runtime type error: deref expects a location but got {v}"
        | .outOfFuel => .outOfFuel
        | .runtimeError msg => .runtimeError msg

      -- Assignment
      -- Pure-mode guard is defense-in-depth (see Expr.newRef note above).
      | Expr.assign e1 e2 =>
        if config.pureMode then
          .runtimeError "assignment forbidden in pure mode"
        else
          match beval (fuel - 1) config e1 verbose with
          | .success config' (Value.loc l) =>
            match beval (fuel - 1) config' e2 verbose with
            | .success config'' (Value.num n) =>
              let config''' := { config'' with memory := config''.memory.update l n }
              .success config''' Value.unit
            | .success _ _ => .runtimeError "Runtime type error: assignment expects number on right side"
            | .outOfFuel => .outOfFuel
            | .runtimeError msg => .runtimeError msg
          | .success _ _ => .runtimeError "Runtime type error: assignment expects location on left side"
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg

      -- Sequencing
      | Expr.seq e1 e2 =>
        match beval (fuel - 1) config e1 verbose with
        | .success config' _v1 =>
          match beval (fuel - 1) config' e2 verbose with
          | .success config'' v2 => .success config'' v2
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg
        | .outOfFuel => .outOfFuel
        | .runtimeError msg => .runtimeError msg

      -- Conditionals
      | Expr.ite e1 e2 e3 =>
        match beval (fuel - 1) config e1 verbose with
        | .success config' (Value.bool true) =>
          match beval (fuel - 1) config' e2 verbose with
          | .success config'' v => .success config'' v
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg
        | .success config' (Value.bool false) =>
          match beval (fuel - 1) config' e3 verbose with
          | .success config'' v => .success config'' v
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg
        | .success _ _ => .runtimeError "Runtime type error: condition must be boolean"
        | .outOfFuel => .outOfFuel
        | .runtimeError msg => .runtimeError msg

      -- Let binding
      | Expr.vlet x e1 e2 =>
        match beval (fuel - 1) config e1 verbose with
        | .success config' v =>
          let config'' := { config' with varEnv := config.varEnv.update x v }
          match beval (fuel - 1) config'' e2 verbose with
          | .success config''' v2 =>
            -- Restore the incoming variable environment, keeping heap/address effects.
            let finalConfig := { config''' with varEnv := config.varEnv }
            .success finalConfig v2
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg
        | .outOfFuel => .outOfFuel
        | .runtimeError msg => .runtimeError msg

      -- Function abstractions
      | Expr.fn x _ body _ =>
        let closure := Value.closure x body config.varEnv
        .success config closure
      | Expr.pfn x _ body _ =>
        let closure := Value.peClosure x body config.varEnv
        .success config closure

      -- Application (call-by-value: evaluate argument first, then function)
      | Expr.app e1 e2 =>
        match beval (fuel - 1) config e2 verbose with
        | .success config' v2 =>
          -- Evaluate the function expression under the caller's variable
          -- environment: argument evaluation may carry heap/address effects
          -- forward, but must not dynamically extend the variable environment
          -- used to evaluate the function expression.
          let functionConfig := { config' with varEnv := config.varEnv }
          match beval (fuel - 1) functionConfig e1 verbose with
          | .success config'' (Value.closure x body env) =>
            -- Extern impure dispatch: body is an extern AST node.
            match body with
            | Expr.externFn id _ argTyp _ _ retSpec _ _ =>
              if config''.pureMode then
                .runtimeError "Pure function cannot apply impure closure"
              else
                match config''.registry.get? id with
                | none => .runtimeError (ExternError.format (.missing id))
                | some (ExternImpl.fn implFn) =>
                  if ¬ valueMatchesTyp v2 argTyp then
                    .runtimeError (ExternError.format (.shapeMismatch id))
                  else
                    let unifiedEnv := VarEnv.update env x v2
                    match implFn unifiedEnv v2 config''.memory config''.nextAddr with
                    | .error err => .runtimeError (ExternError.format err)
                    | .ok (v, mem', addr') =>
                      match validateExternReturn id retSpec v with
                      | .error err => .runtimeError (ExternError.format err)
                      | .ok v' =>
                        .success { config'' with memory := mem', nextAddr := addr' } v'
                | some _ => .runtimeError (ExternError.format (.kindMismatch id))
            | _ =>
              if config''.pureMode then
                .runtimeError "Pure function cannot apply impure closure"
              else
                -- Restore the caller's variable environment for the body result.
                let bodyReturnConfig := { config'' with varEnv := config.varEnv }
                bevalFunctionBody (fuel - 1) verbose bodyReturnConfig env x v2 body false
          | .success config'' (Value.peClosure x body env) =>
            -- Extern pure dispatch: body is an extern AST node.
            match body with
            | Expr.externPfn id _ argTyp _ _ retSpec _ =>
              match config''.registry.get? id with
              | none => .runtimeError (ExternError.format (.missing id))
              | some (ExternImpl.pfn implFn) =>
                if ¬ valueMatchesTyp v2 argTyp then
                  .runtimeError (ExternError.format (.shapeMismatch id))
                else
                  let unifiedEnv := VarEnv.update env x v2
                  match implFn unifiedEnv v2 config''.memory with
                  | .error err => .runtimeError (ExternError.format err)
                  | .ok v =>
                    match validateExternReturn id retSpec v with
                    | .error err => .runtimeError (ExternError.format err)
                    | .ok v' => .success config'' v'
              | some _ => .runtimeError (ExternError.format (.kindMismatch id))
            | _ =>
              match Expr.toPExpr? body with
              | some _ =>
                -- Restore the caller's variable environment for the body result.
                let bodyReturnConfig := { config'' with varEnv := config.varEnv }
                bevalFunctionBody (fuel - 1) verbose bodyReturnConfig env x v2 body true
              | none => .runtimeError "Pure closure body is not pure"
          | .success _ _ => .runtimeError "Runtime type error: expected function in application"
          | .outOfFuel => .outOfFuel
          | .runtimeError msg => .runtimeError msg
        | .outOfFuel => .outOfFuel
        | .runtimeError msg => .runtimeError msg

      -- Extern declarations: look up in the registry and produce a runtime
      -- value. See `doc/ffi-proposal.md`.
      | Expr.externVal id typ _poison _pred =>
        match config.registry.get? id with
        | none => .runtimeError (ExternError.format (.missing id))
        | some (ExternImpl.val v) =>
            if valueMatchesTyp v typ then .success config v
            else .runtimeError (ExternError.format (.shapeMismatch id))
        | some _ => .runtimeError (ExternError.format (.kindMismatch id))
      | Expr.externRef id _refPoison _refPred _cellPoison _cellPred =>
        -- A reference-valued extern: the registry supplies a stable location
        -- value for the external cell (e.g. `errno`).  Runtime behaviour is
        -- identical to `extern val` at type `ref int`.
        match config.registry.get? id with
        | none => .runtimeError (ExternError.format (.missing id))
        | some (ExternImpl.val v) =>
            if valueMatchesTyp v (Typ.ref Typ.int) then .success config v
            else .runtimeError (ExternError.format (.shapeMismatch id))
        | some _ => .runtimeError (ExternError.format (.kindMismatch id))
      | Expr.externFn id argName argTyp argPoison argPred retSpec effects captures =>
        match config.registry.get? id with
        | none => .runtimeError (ExternError.format (.missing id))
        | some (ExternImpl.fn _) =>
            .success config
              (Value.closure argName
                (Expr.externFn id argName argTyp argPoison argPred retSpec effects captures) config.varEnv)
        | some _ => .runtimeError (ExternError.format (.kindMismatch id))
      | Expr.externPfn id argName argTyp argPoison argPred retSpec captures =>
        match config.registry.get? id with
        | none => .runtimeError (ExternError.format (.missing id))
        | some (ExternImpl.pfn _) =>
            .success config
              (Value.peClosure argName
                (Expr.externPfn id argName argTyp argPoison argPred retSpec captures) config.varEnv)
        | some _ => .runtimeError (ExternError.format (.kindMismatch id))

  /-- Helper for evaluating function bodies (impure vs pure) -/
  def bevalFunctionBody (fuel : Nat) (verbose : Bool)
                        (currentConfig : Config) (closureEnv : VarEnv)
                        (paramName : Name) (argValue : Value) (body : Expr)
                        (isPure : Bool) : EvalResult :=
    match fuel with
    | 0 => .outOfFuel
    | fuel' + 1 =>
      let updatedEnv := VarEnv.update closureEnv paramName argValue
      let bodyConfig := { currentConfig with varEnv := updatedEnv, pureMode := isPure }
      match beval fuel' bodyConfig body verbose with
      | .success evalConfig v =>
        if isPure then
          -- Restore caller's pureMode (pure bodies stay pure when caller is pure)
          .success ({ currentConfig with pureMode := currentConfig.pureMode }) v
        else
          let finalConfig := { currentConfig with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := currentConfig.pureMode }
          .success finalConfig v
      | .outOfFuel => .outOfFuel
      | .runtimeError msg => .runtimeError msg

end -- mutual

/- Convenience runner that returns EvalResult from an empty initial state.
   Uses an empty extern registry — callers that need registered externs should
   call `beval` directly with a `Config` carrying a populated registry. -/
def runBig (fuel : Nat) (expr : Expr) (verbose : Bool := false) : EvalResult :=
  let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0, false, emptyExternRegistry⟩
  beval fuel initialConfig expr verbose

end LeanPoison
