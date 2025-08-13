/- Small-step operational semantics for LeanPoison -/
/- Each reduction case corresponds to a rule in poison-lang.ott -/

import LeanPoison.Syntax
import LeanPoison.Runtime
import Std.Data.HashMap
open Std

-- Helper functions for operations
def evalOp (op : Op) (v1 v2 : Value) : Option Value :=
  match op with
  | Op.add =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.num (n1 + n2))
    | _, _ => none
  | Op.gte =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.bool (n1 >= n2))
    | _, _ => none

  | Op.gt =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.bool (n1 > n2))
    | _, _ => none
  | Op.lte =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.bool (n1 <= n2))
    | _, _ => none
  | Op.lt =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.bool (n1 < n2))
    | _, _ => none
  | Op.mul =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.num (n1 * n2))
    | _, _ => none
  | Op.div =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.num (n1 / n2))
    | _, _ => none
  | Op.eq =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.bool (n1 == n2))
    | _, _ => none
  | Op.sub =>
    match v1, v2 with
    | Value.num n1, Value.num n2 => some (Value.num (n1 - n2))
    | _, _ => none
  | Op.or =>
    match v1,v2 with
    | Value.bool b1 , Value.bool b2 => some (Value.bool (b1 || b2))
    | _,_ => none
  | Op.and =>
    match v1,v2 with
    | Value.bool b1 , Value.bool b2 => some (Value.bool (b1 && b2))
        | _,_ => none

-- Result of a single evaluation step
inductive StepResult where
  | progress : Config → ExprOrValue → StepResult      -- Successful reduction
  | stuck : StepResult                                -- Cannot reduce (value or error)
  | error : String → StepResult                       -- Explicit error

-- Wrapper function to print return values
def stepReturn (fuel : Nat) (verbose : Bool) (result : StepResult) : StepResult :=
  if verbose then
    match result with
    | StepResult.progress config' ev' =>
      dbg_trace s!"← step [{fuel}]:\t⟨{repr ev'}⟩";
      StepResult.progress config' ev'
    | StepResult.stuck =>
      dbg_trace s!"← step [{fuel}]:\tstuck";
      StepResult.stuck
    | StepResult.error msg =>
      dbg_trace s!"← step [{fuel}]:\terror: {msg}";
      StepResult.error msg
  else
    result

def stepEntryTrace (fuel : Nat) (verbose : Bool) (_config : Config) (ev : ExprOrValue) : Unit :=
  if verbose then dbg_trace s!"→ Step [{fuel}]:\t⟨{repr ev}⟩"; () else ()


mutual

-- Small-step reduction relation: ⟨e, m, r⟩ → ⟨ev', m', r'⟩
-- Returns the result of attempting one reduction step
def step (fuel : Nat) (verbose : Bool) (config : Config) (ev : ExprOrValue) : IO StepResult :=
  do
  let _ := stepEntryTrace fuel verbose config ev
  if fuel = 0 then
    --dbg_trace s!"out of fuel";
    return stepReturn fuel verbose (StepResult.error "out of fuel")
  else
    match ev with
  -- Values are stuck (cannot reduce)
  | ExprOrValue.value _ => return stepReturn fuel verbose StepResult.stuck
  | ExprOrValue.expr expr =>
    match expr with
    -- Rule: lit_num (OTT rule 265-266)
    -- ---------------------- :: lit_num
    -- <n, m, r> -> <value n, m, r>
    | Expr.num n => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value (Value.num n)))

    -- Rule: lit_bool (OTT rule 268-269)
    -- ---------------------- :: lit_bool
    -- <b, m, r> -> <value b, m, r>
    | Expr.bool b => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value (Value.bool b)))

    -- Rule: lit_unit (OTT rule 271-272)
    -- ---------------------- :: lit_unit
    -- <unit, m, r> -> <value unit, m, r>
    | Expr.unit => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value Value.unit))

    -- Rule: var (OTT rule 410-411)
    -- r(x) = v
    -- --------------------------- :: var
    -- < x, m, r > -> < value v, m, r >
    | Expr.var x =>
            match config.varEnv x with
      | some v => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value v))
      | none =>
        return stepReturn fuel verbose (StepResult.error s!"var {x} not found")

    -- Rule: op_plus, op_minus, op_mult, op_div, op_gteq, op_lteq, op_gt, op_lt, op_eq, op_and, op_or
    -- (OTT rules 276-337)
    -- <e1,m,r> -> <value v1, m',r'>
    -- <e2,m',r'> -> <value v2, m'',r''>
    -- n = v1 op v2  (or b = v1 op v2 for comparisons)
    -- ---------------------- :: op_*
    -- <e1 op e2, m, r> -> <value n, m'', r''>
    | Expr.op e1 op e2 =>
      -- Check if both operands are values
      match e1.toValue?, e2.toValue? with
      | some v1, some v2 =>
        match evalOp op v1 v2 with
        | some v => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value v))
        | none => return stepReturn fuel verbose (StepResult.error "type error in operation")
      -- Rule: op_reduce_right (OTT rule 346-348)
      -- <e2,m,r> -> <expr e2',m',r'>
      -- ------------------------------- :: op_reduce_right
      -- <e1 op e2,m,r> -> <expr (e1 op e2'),m',r'>
      | some v1, none =>
        match (<- step (fuel - 1) verbose config (ExprOrValue.expr e2)) with
        | StepResult.progress config' ev2' =>
          match ev2' with
          | ExprOrValue.expr e2' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.op e1 op e2')))
          | ExprOrValue.value v2 =>
            -- Right operand reduced to value, retry the operation
            match evalOp op v1 v2 with
            | some v => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.value v))
            | none => return stepReturn fuel verbose (StepResult.error "type error in operation")
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

      -- Rule: op_reduce_left (OTT rule 341-343)
      -- <e1,m,r> -> <expr e1',m',r'>
      -- ------------------------------- :: op_reduce_left
      -- <e1 op e2,m,r> -> <expr (e1' op e2),m',r'>
      | none, _ =>
        match <- step (fuel - 1) verbose config (ExprOrValue.expr e1) with
        | StepResult.progress config' ev1' =>
          match ev1' with
          | ExprOrValue.expr e1' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.op e1' op e2)))
          | ExprOrValue.value v1 =>
            -- Left operand reduced to value, check right
            match e2.toValue? with
            | some v2 =>
              -- Both are values now
              match evalOp op v1 v2 with
              | some v => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.value v))
              | none => return stepReturn fuel verbose (StepResult.error "type error in operation")
            | none =>
              -- Left is value, right needs evaluation - reconstruct with literal
              let e1' := match v1 with
                | Value.num n => Expr.num n
                | Value.bool b => Expr.bool b
                | Value.unit => Expr.unit
                | _ => e1  -- Should not happen for operations
              return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.op e1' op e2)))
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

    -- Rule: if_true, if_false, if_reduce_cond (OTT rules 393-403)
    -- <e,m,r> -> <value true, m',r'>
    -- ---------------------------------------------- :: if_true
    -- < if e then e1 else e2, m, r > -> < expr e1, m', r' >
    --
    -- <e,m,r> -> <value false, m',r'>
    -- ---------------------------------------------- :: if_false
    -- < if e then e1 else e2, m, r > -> < expr e2, m', r' >
    | Expr.ite e1 e2 e3 =>
      match e1 with
      | Expr.bool true => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.expr e2))
      | Expr.bool false => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.expr e3))
      | _ =>
        -- Rule: if_reduce_cond (OTT rule 401-403)
        -- <e,m,r> -> <expr e',m',r'>
        -- ------------------------------------------------------------ :: if_reduce_cond
        -- < if e then e1 else e2, m, r > -> < expr (if e' then e1 else e2), m', r' >
        match <- step (fuel - 1) verbose config (ExprOrValue.expr e1) with
        | StepResult.progress config' ev1' =>
          match ev1' with
          | ExprOrValue.expr e1' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.ite e1' e2 e3)))
          | ExprOrValue.value (Value.bool true) => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr e2))
          | ExprOrValue.value (Value.bool false) => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr e3))
          | _ => return stepReturn fuel verbose (StepResult.error "type error: condition must be boolean")
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

    -- Rule: ref (OTT rule 356-359)
    -- <e,m,r> -> <value n, m',r'>
    -- fresh l
    -- ------------------------------ :: ref
    -- <ref e,m,r> -> <value l, m' [ l |-> n ], r'>
    | Expr.newRef e =>
      match e with
      | Expr.num n =>
        let (l, config') := freshLoc config
        let config'' := { config' with memory := config'.memory.update l n }
        return stepReturn fuel verbose (StepResult.progress config'' (ExprOrValue.value (Value.loc l)))

      -- Rule: ref_reduce_arg (OTT rule 351-353)
      -- <e,m,r> -> <expr e',m',r'>
      -- ------------------------------ :: ref_reduce_arg
      -- <ref e,m,r> -> <expr (ref e'),m',r'>
      | _ =>
        match <- step (fuel - 1) verbose config (ExprOrValue.expr e) with
        | StepResult.progress config' ev' =>
          match ev' with
          | ExprOrValue.expr e' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.newRef e')))
          | ExprOrValue.value (Value.num n) =>
            let (l, config'') := freshLoc config'
            let config''' := { config'' with memory := config''.memory.update l n }
            return stepReturn fuel verbose (StepResult.progress config''' (ExprOrValue.value (Value.loc l)))
          | _ => return stepReturn fuel verbose (StepResult.error "type error: ref expects a number")
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

    -- Rule: deref (dereference an expression)
    -- We need to check if the expression evaluates to a location
    | Expr.deref e =>
      match e.toValue? with
      | some (Value.loc l) =>
        -- Rule: deref (OTT rule 362-364)
        -- <e,m,r> -> <value l,m',r'>
        -- m'(l) = n
        -- ------------------------------ :: deref
        -- <!e,m,r> -> <value n,m',r'>
        match config.memory.get? l with
        | some n => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value (Value.num n)))
        | none =>
          --dbg_trace s!"deref {l} not found";
          -- Dereferencing a location that is not in the memory returns default value 0
          -- this is an example of poisoned value
          return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value (Value.num 0)))
      | _ =>
        -- Rule: deref_reduce (OTT rule 366-368)
        -- <e,m,r> -> <expr e',m',r'>
        -- ------------------------------ :: deref_reduce
        -- <!e,m,r> -> <expr (!e'),m',r'>
        match <- step (fuel - 1) verbose config (ExprOrValue.expr e) with
        | StepResult.progress config' ev' =>
          match ev' with
          | ExprOrValue.expr e' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.deref e')))
          | ExprOrValue.value (Value.loc l) =>
            match config'.memory.get? l with
            | some n => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.value (Value.num n)))
            | none => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.value (Value.num 0)))
          | _ => return stepReturn fuel verbose (StepResult.error "type error: deref expects a location")
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

        -- Rule: assign (OTT rule 371-373)
    -- <e1,m,r> -> <value l, m',r'>
    -- <e2,m',r'> -> <value n, m'',r''>
    -- -------------------------------------- :: assign
    -- < e1 := e2, m, r > -> <value unit, m'' [ l |-> n ], r'' >
    | Expr.assign e1 e2 =>
      -- The OTT rules specify we should evaluate e1 first, then e2
      -- We need a two-phase approach:
      -- 1. Evaluate e1 to get a location
      -- 2. Evaluate e2 to get a value
      -- 3. Perform the assignment

      -- First, try to evaluate e1 to a value
      let evalE1 := step (fuel - 1) verbose config (ExprOrValue.expr e1)
      match <- evalE1 with
      | StepResult.progress config' (ExprOrValue.value (Value.loc l)) =>
        -- e1 evaluated to a location, now evaluate e2
        let evalE2 := step (fuel - 1) verbose config' (ExprOrValue.expr e2)
        match <- evalE2 with
        | StepResult.progress config'' (ExprOrValue.value (Value.num n)) =>
          -- Both are values, perform assignment
          let config''' := { config'' with memory := config''.memory.update l n }
          return stepReturn fuel verbose (StepResult.progress config''' (ExprOrValue.value Value.unit))
        | StepResult.progress _config'' (ExprOrValue.value _) =>
          return stepReturn fuel verbose (StepResult.error "type error: assignment expects number on right side")
        | StepResult.progress config'' (ExprOrValue.expr e2') =>
          -- e2 still needs evaluation
          -- Problem: we can't represent "loc l := e2'" in our AST
          -- Workaround: Use eval to fully evaluate e2 before assignment
          let (finalConfig, result) <- eval (fuel - 2) config'' (ExprOrValue.expr e2') verbose
          match result with
          | ExprOrValue.value (Value.num n) =>
            let assignConfig := { finalConfig with memory := finalConfig.memory.update l n }
            return stepReturn fuel verbose (StepResult.progress assignConfig (ExprOrValue.value Value.unit))
          | _ =>
            return stepReturn fuel verbose (StepResult.error "assignment right side did not evaluate to number")
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)
      | StepResult.progress _config' (ExprOrValue.value _) =>
        return stepReturn fuel verbose (StepResult.error "type error: assignment expects location on left side")
      | StepResult.progress config' (ExprOrValue.expr e1') =>
        -- e1 still needs evaluation, reduce it first (assign_reduce_left)
        return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.assign e1' e2)))
      | StepResult.stuck =>
        -- e1 is already a value, check if it's a location
        match e1.toValue? with
        | some (Value.loc l) =>
          -- Now evaluate e2
          match e2.toValue? with
          | some (Value.num n) =>
            let config' := { config with memory := config.memory.update l n }
            return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.value Value.unit))
          | _ =>
            -- e2 needs evaluation (assign_reduce_right)
            match <- step (fuel - 1) verbose config (ExprOrValue.expr e2) with
            | StepResult.progress config' ev2' =>
              match ev2' with
              | ExprOrValue.expr e2' =>
                return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.assign e1 e2')))
              | ExprOrValue.value (Value.num n) =>
                let config'' := { config' with memory := config'.memory.update l n }
                return stepReturn fuel verbose (StepResult.progress config'' (ExprOrValue.value Value.unit))
              | _ => return stepReturn fuel verbose (StepResult.error "type error: assignment expects number")
            | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
            | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)
        | _ => return stepReturn fuel verbose StepResult.stuck
      | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

    -- Rule: seq (sequence expressions)
    | Expr.seq e1 e2 =>
      match e1.toValue? with
      -- Rule: seq_value (OTT rule 389-391)
      -- <e1,m,r> -> <value v, m',r'>
      -- -------------------------------------- :: seq_value
      -- < e1 ; e2, m, r > -> < expr e2, m', r' >
      | some _v => return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.expr e2))
      | none =>
        -- Rule: seq_reduce_first (OTT rule 384-386)
        -- <e1,m,r> -> <expr e1',m',r'>
        -- -------------------------------------- :: seq_reduce_first
        -- < e1 ; e2, m, r > -> < expr (e1' ; e2), m', r' >
        match <- step (fuel - 1) verbose config (ExprOrValue.expr e1) with
        | StepResult.progress config' ev1' =>
          match ev1' with
          | ExprOrValue.expr e1' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.seq e1' e2)))
          | ExprOrValue.value _v => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr e2))
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

    -- Rule: while (OTT rule 405-406)
    -- --------------------------------------------------------------------------- :: while
    -- < while e1 do e2, m, r> -> < expr (if e1 then ( e2 ; while e1 do e2 ) else unit), m, r >
    | Expr.while e1 e2 =>
      let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.while e1 e2)) Expr.unit
      return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.expr unfolded))

    -- Rule: let (let binding)
    | Expr.let x e1 e2 =>
      match e1.toValue? with
      -- Rule: let_value (OTT rule 419-421)
      -- <e1,m,r> -> <value v, m',r'>
      -- -------------------------------------------------------- :: let_value
      -- < let x = e1 in e2, m, r > -> < expr e2, m', r'[x |-> v] >
      | some v =>
        let config' := { config with varEnv := config.varEnv.update x v }
        return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr e2))
      | none =>
        -- Rule: let_reduce_arg (OTT rule 414-416)
        -- <e1,m,r> -> <expr e1',m',r'>
        -- -------------------------------------------------------- :: let_reduce_arg
        -- < let x = e1 in e2, m, r > -> < expr (let x = e1' in e2), m', r' >
        match <- step (fuel - 1) verbose config (ExprOrValue.expr e1) with
        | StepResult.progress config' ev1' =>
          match ev1' with
          | ExprOrValue.expr e1' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.let x e1' e2)))
          | ExprOrValue.value v =>
            let config'' := { config' with varEnv := config'.varEnv.update x v }

            return stepReturn fuel verbose (StepResult.progress config'' (ExprOrValue.expr e2))
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

    -- Rule: fn_abs (OTT rule 423-425)
    -- --------------------------------------------------------------- :: fn_abs
    -- < fn x : ST1 => e : ST2, m, r > -> < value closure(x, e, r), m, r >
    | Expr.fn x _paramType body _returnType =>

      let closure := Value.closure x body config.varEnv
      return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value closure))

    -- Rule: pfn_abs (OTT rule 427-429)
    -- --------------------------------------------------------------- :: pfn_abs
    -- < pfn x : ST1 => pe : ST2, m, r > -> < value pe_closure(x, pe, r), m, r >
    | Expr.pfn x _paramType body _returnType =>
      let closure := Value.peClosure x body config.varEnv
      return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value closure))

    -- Function application rules - evaluate argument first (call-by-value)
    | Expr.app e1 e2 =>
      match e2.toValue? with
      | none =>
        -- Rule: app_reduce_arg (OTT rule 432-434)
        -- <e2,m,r> -> <expr e2',m',r'>
        -- --------------------------------------------------------------- :: app_reduce_arg
        -- < e1 e2, m, r > -> < expr (e1 e2'), m', r' >
        match <- step (fuel - 1) verbose config (ExprOrValue.expr e2) with
        | StepResult.progress config' ev2' =>
          match ev2' with
          | ExprOrValue.expr e2' =>
            return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.app e1 e2')))
          | ExprOrValue.value v2 =>
            -- Argument is now a value, move to evaluating the function
            -- This is continuation of app_reduce_arg followed by app_reduce_func
            match e1.toValue? with
            | none =>
              -- Need to evaluate function
              match <- step (fuel - 1) verbose config' (ExprOrValue.expr e1) with
              | StepResult.progress config'' ev1' =>
                match ev1' with
                | ExprOrValue.expr e1' =>
                  -- Function still needs evaluation
                  return stepReturn fuel verbose (StepResult.progress config'' (ExprOrValue.expr (Expr.app e1' e2)))
                | ExprOrValue.value v1 =>
                  -- Both are now values, apply
                  match v1 with
                  | Value.closure x body env =>
                    -- Use closure's captured environment, not current environment
                    let closureConfig := { config'' with varEnv := VarEnv.update env x v2 }
                    let (evalConfig, ev') <- eval (fuel-1) closureConfig (ExprOrValue.expr body) verbose
                    -- Preserve original environment, only take memory changes
                    let finalConfig := { config'' with memory := evalConfig.memory, nextLoc := evalConfig.nextLoc }
                    return stepReturn fuel verbose (StepResult.progress finalConfig ev')
                  | Value.peClosure x body env =>
                    let tempConfig := { config'' with varEnv := VarEnv.update env x v2 }
                    let (_finalConfig, ev') <- eval (fuel-1) tempConfig (ExprOrValue.expr body) verbose
                    return stepReturn fuel verbose (StepResult.progress config'' ev')
                  | _ =>
                    return stepReturn fuel verbose (StepResult.error "type error: expected function in application")
              | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
              | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)
            | some v1 =>
              -- Function is already a value, apply
              match v1 with
              | Value.closure x body env =>
                -- Use only the closure's environment plus the argument
                let closureConfig := { config' with varEnv := VarEnv.update env x v2 }
                let (config''', ev') <- eval (fuel-1) closureConfig (ExprOrValue.expr body) verbose
                -- Preserve original environment, only take memory changes
                let finalConfig := { config' with memory := config'''.memory, nextLoc := config'''.nextLoc }
                return stepReturn fuel verbose (StepResult.progress finalConfig ev')
              | Value.peClosure x body env =>
                let tempConfig := { config' with varEnv := VarEnv.update env x v2 }
                let (_finalConfig, ev') <- eval (fuel-1) tempConfig (ExprOrValue.expr body) verbose
                return stepReturn fuel verbose (StepResult.progress config' ev')
              | _ =>
                return stepReturn fuel verbose (StepResult.error "type error: expected function in application")
        | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
        | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)
      | some v2 =>
        -- Argument is a value, now check function
        match e1.toValue? with
        | some (Value.closure x body env) =>
          -- Rule: app_closure_value (OTT rule 444-448)
          -- Both function and argument are values, apply
          -- Use only the closure's environment plus the argument
          let closureConfig := { config with varEnv := VarEnv.update env x v2 }
          let (config'', ev') <- eval (fuel-1) closureConfig (ExprOrValue.expr body) verbose
          -- Preserve original environment, only take memory changes
          let finalConfig := { config with memory := config''.memory, nextLoc := config''.nextLoc }
          return stepReturn fuel verbose (StepResult.progress finalConfig ev')
        | some (Value.peClosure x body env) =>
          -- Rule: app_pure_closure_value (OTT rule 455-460)
          -- Pure function application - no side effects
          let tempConfig := { config with varEnv := VarEnv.update env x v2 }
          let (_finalConfig, ev') <- eval (fuel-1) tempConfig (ExprOrValue.expr body) verbose
          -- Return original config to preserve no side effects for pure functions
          return stepReturn fuel verbose (StepResult.progress config ev')
        -- Non-function values in function position
        | some (Value.num _)
        | some (Value.bool _)
        | some (Value.unit)
        | some (Value.loc _) =>
          return stepReturn fuel verbose (StepResult.error "type error: expected function in application")
        | none =>
          -- Rule: app_reduce_func (OTT rule 437-441)
          -- <e2,m,r> -> <value v,m',r'>
          -- <e1,m',r'> -> <expr e1',m'',r''>
          -- --------------------------------------------------------------- :: app_reduce_func
          -- < e1 e2, m, r > -> < expr (e1' e2), m'', r'' >
          match <- step (fuel - 1) verbose config (ExprOrValue.expr e1) with
          | StepResult.progress config' ev1' =>
            match ev1' with
            | ExprOrValue.expr e1' =>
              return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.app e1' e2)))
            | ExprOrValue.value v1 =>
              -- Function is now a value, apply it
              match v1 with
              | Value.closure x body env =>
                let config'' := { config' with varEnv := VarEnv.update env x v2 }
                let (config''', ev') <- eval (fuel-1) config'' (ExprOrValue.expr body) verbose
                -- Preserve original environment, only take memory changes
                let finalConfig := { config' with memory := config'''.memory, nextLoc := config'''.nextLoc }
                return stepReturn fuel verbose (StepResult.progress finalConfig ev')
              | Value.peClosure x body env =>
                let tempConfig := { config' with varEnv := VarEnv.update env x v2 }
                let (_finalConfig, ev') <- eval (fuel-1) tempConfig (ExprOrValue.expr body) verbose
                -- Return original config' to preserve no side effects for pure functions
                return stepReturn fuel verbose (StepResult.progress config' ev')
              | _ =>
                return stepReturn fuel verbose (StepResult.error "type error: expected function in application")
          | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
          | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

    -- Built-in expressions
    | Expr.builtIn builtin =>
      match builtin with
      | builtInExpr.rand e =>
        match e.toValue? with
        -- Rule: rand_value (OTT rule 468-471)
        -- <e,m,r> -> <value n, m',r'>
        -- n' = random n
        -- --------------------------------------------------------------- :: rand_value
        -- <rand e,m,r> -> <value n', m',r'>
        | some (Value.num n) =>
          if n >= 0 then
            do
              let r <- (IO.rand 0 n.toNat).toIO   -- r : Nat
              let randomNo := Int.ofNat r  -- convert Nat to Int
              return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value (Value.num randomNo)))
          else
            IO.println "Argument to rand must evaluate to non negative integer"
            return stepReturn fuel verbose (StepResult.error "Argument to rand must evaluate to non negative integer")
        | _ =>
          -- Rule: rand_arg_reduce (OTT rule 463-465)
          -- <e,m,r> -> <expr e',m',r'>
          -- --------------------------------------------------------------- :: rand_arg_reduce
          -- <rand e,m,r> -> <expr (rand e'),m',r'>
          match <- step (fuel - 1) verbose config (ExprOrValue.expr e) with
          | StepResult.progress config' ev' =>
            match ev' with
            | ExprOrValue.expr e' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.builtIn (builtInExpr.rand e'))))
            | ExprOrValue.value (Value.num n) =>
              if n >= 0 then
                do
                  let r <- (IO.rand 0 n.toNat).toIO
                  let randomNo := Int.ofNat r
                  return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.value (Value.num randomNo)))
              else
                return stepReturn fuel verbose (StepResult.error "Argument to rand must evaluate to non negative integer")
            | _ => return stepReturn fuel verbose (StepResult.error "type error: rand expects a number")
          | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
          | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)

      | builtInExpr.frand e =>
        match e.toValue? with
        -- Rule: frand_value (OTT rule 481-484)
        -- <e,m,r> -> <value n, m',r'>
        -- n' = random n
        -- --------------------------------------------------------------- :: frand_value
        -- <frand e,m,r> -> <value n', m',r'>
        -- The syntactic definition is the same as rand but the implementation is faulty
        | some (Value.num n) =>
          if n >= 0 then
            do
              let maxRange : Nat := 4 * (n.toNat)
              let r <- (IO.rand 0 maxRange).toIO   --   0 <= r <= 4n
              let randomNo : Int := (Int.ofNat r) - (2 * n)  --  -2n <= randomNo <= 2n
              return stepReturn fuel verbose (StepResult.progress config (ExprOrValue.value (Value.num randomNo)))
          else
            IO.println "Argument to frand must evaluate to non negative integer"
            return stepReturn fuel verbose (StepResult.error "Argument to frand must evaluate to non negative integer")
        | _ =>
          -- Rule: frand_arg_reduce (OTT rule 475-477)
          -- <e,m,r> -> <expr e',m',r'>
          -- --------------------------------------------------------------- :: frand_arg_reduce
          -- <frand e,m,r> -> <expr (frand e'),m',r'>
          match <- step (fuel - 1) verbose config (ExprOrValue.expr e) with
          | StepResult.progress config' ev' =>
            match ev' with
            | ExprOrValue.expr e' => return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.expr (Expr.builtIn (builtInExpr.frand e'))))
            | ExprOrValue.value (Value.num n) =>
              if n >= 0 then
                do
                  let maxRange : Nat := 4 * (n.toNat)
                  let r <- (IO.rand 0 maxRange).toIO
                  let randomNo : Int := (Int.ofNat r) - (2 * n)
                  return stepReturn fuel verbose (StepResult.progress config' (ExprOrValue.value (Value.num randomNo)))
              else
                return stepReturn fuel verbose (StepResult.error "Argument to frand must evaluate to non negative integer")
            | _ => return stepReturn fuel verbose (StepResult.error "type error: frand expects a number")
          | StepResult.stuck => return stepReturn fuel verbose StepResult.stuck
          | StepResult.error msg => return stepReturn fuel verbose (StepResult.error msg)
termination_by fuel
-- Multi-step evaluation
def eval (fuel : Nat) (config : Config) (ev : ExprOrValue) (verbose : Bool) : IO (Config × ExprOrValue) := do
  if fuel < 2 then
    return (config, ev)
  else
    match <- step (fuel - 1) verbose config ev with
    | StepResult.progress config' ev' =>
      eval (fuel - 2) config' ev' verbose
    | StepResult.stuck =>
      return (config, ev)
    | StepResult.error msg => do
      if verbose then IO.println s!"Evaluation error: {msg}"
      return (config, ev)
termination_by fuel

end -- mutual (step, eval)

-- Helper to run an expression with empty environments
def run (fuel : Nat) (expr : Expr) (verbose : Bool := false) : IO (Config × ExprOrValue) :=
  let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0⟩
  eval fuel initialConfig (ExprOrValue.expr expr) verbose
