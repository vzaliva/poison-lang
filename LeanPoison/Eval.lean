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

-- Wrapper function to print return values
def stepReturn (fuel : Nat) (verbose : Bool) (result : Option (Config × Expr)) : Option (Config × Expr) :=
  if verbose then
    match result with
    | some (config', expr') =>
      dbg_trace s!"← step [{fuel}]:\t⟨{repr expr'}⟩";
      some (config', expr')
    | none =>
      dbg_trace s!"← step [{fuel}]:\tstuck";
      none
  else
    result

def stepEntryTrace (fuel : Nat) (verbose : Bool) (_config : Config) (expr : Expr) : Unit :=
  if verbose then dbg_trace s!"→ Step [{fuel}]:\t⟨{repr expr}⟩"; () else ()


mutual

-- Small-step reduction relation: ⟨e, m, r⟩ → ⟨e', m', r'⟩
-- Returns None if the expression cannot be reduced (is stuck or a value)
def step (fuel : Nat) (verbose : Bool) (config : Config) (expr : Expr) : Option (Config × Expr) :=
  let _ := stepEntryTrace fuel verbose config expr
  if fuel = 0 then
    dbg_trace s!"out of fuel";
    stepReturn fuel verbose none
  else
    match expr with
  -- Values are stuck (cannot reduce)
  | Expr.value _ => stepReturn fuel verbose none

  -- Rule: var
  -- r(x) = v
  -- ------------------------
  -- ⟨ x, m, r ⟩ → ⟨ v, m, r ⟩
  | Expr.var x =>
    match config.varEnv x with
    | some v => stepReturn fuel verbose (some (config, v.toExpr))
    | none =>
      dbg_trace s!"var {x} not found";
      stepReturn fuel verbose none

  -- Rule: op_plus and op_gteq (when both operands are values)
  -- n1 + n2 = n
  -- ------------------------
  -- ⟨n1 + n2, m, r⟩ → ⟨n, m, r⟩
  | Expr.op (Expr.value v1) op (Expr.value v2) =>
    match evalOp op v1 v2 with
    | some v => stepReturn fuel verbose (some (config, v.toExpr))
    | none => stepReturn fuel verbose none

  -- Rule: op2 (evaluate right operand when left is a value)
  -- ⟨e2,m,r⟩ → ⟨e2',m',r'⟩
  -- -------------------------------
  -- ⟨v1 op e2,m,r⟩ → ⟨v1 op e2',m',r'⟩
  | Expr.op (Expr.value v1) op e2 =>
    match step (fuel - 1) verbose config e2 with
    | some (config', e2') => stepReturn fuel verbose (some (config', Expr.op (Expr.value v1) op e2'))
    | none => stepReturn fuel verbose none

  -- Rule: op1 (evaluate left operand first)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- -------------------------------
  -- ⟨e1 op e2,m,r⟩ → ⟨e1' op e2,m',r'⟩
  | Expr.op e1 op e2 =>
    match step (fuel - 1) verbose config e1 with
    | some (config', e1') => stepReturn fuel verbose (some (config', Expr.op e1' op e2))
    | none => stepReturn fuel verbose none

  -- Rule: if1, if2, if3
  -- --------------------------------
  -- ⟨ if true then e1 else e2, m, r ⟩ → ⟨ e1, m, r ⟩
  -- ⟨ if false then e1 else e2, m, r ⟩ → ⟨ e2, m, r ⟩
  | Expr.ite (Expr.value (Value.bool true)) e2 _e3 => stepReturn fuel verbose (some (config, e2))
  | Expr.ite (Expr.value (Value.bool false)) _e2 e3 => stepReturn fuel verbose (some (config, e3))
  | Expr.ite e1 e2 e3 =>
    -- Rule: if3 (evaluate condition)
    -- ⟨e,m,r⟩ → ⟨e',m',r'⟩
    -- ------------------------------------------------------------
    -- ⟨ if e then e1 else e2, m, r ⟩ → ⟨ if e' then e1 else e2, m', r' ⟩
    match step (fuel - 1) verbose config e1 with
    | some (config', e1') => stepReturn fuel verbose (some (config', Expr.ite e1' e2 e3))
    | none => stepReturn fuel verbose none

  -- Rule: ref (allocate new reference when argument is a value)
  -- fresh l
  -- ------------------------------
  -- ⟨ref n,m,r⟩ → ⟨l, m [ l |-> n ], r⟩
  | Expr.newRef (Expr.value (Value.num n)) =>
    let l := config.nextLoc
    let config' := { config with
      memory := config.memory.update l n,
      nextLoc := l + 1
    }
    stepReturn fuel verbose (some (config', Expr.loc l))

  -- Rule: ref_eval (evaluate argument of ref)
  -- ⟨e,m,r⟩ → ⟨e',m',r'⟩
  -- ------------------------------
  -- ⟨ref e,m,r⟩ → ⟨ref e',m',r'⟩
  | Expr.newRef e =>
    match step (fuel - 1) verbose config e with
    | some (config', e') => stepReturn fuel verbose (some (config', Expr.newRef e'))
    | none => stepReturn fuel verbose none

  -- Rule: deref_loc (dereference a location)
  -- m(l) = n
  -- ------------------------------
  -- ⟨!l,m,r⟩ → ⟨n,m,r⟩
  | Expr.deref (Expr.value (Value.loc l)) =>
    match config.memory.get? l with
    | some n => stepReturn fuel verbose (some (config, Expr.num n))
    | none =>
      dbg_trace s!"deref {l} not found";
      -- Dereferencing a location that is not in the memory returns default value 0
      -- this is an example of poisoned value
      stepReturn fuel verbose (some (config, Expr.num 0))

  -- Rule: deref_eval (evaluate argument of deref)
  -- ⟨e,m,r⟩ → ⟨e',m',r'⟩
  -- ------------------------------
  -- ⟨!e,m,r⟩ → ⟨!e',m',r'⟩
  | Expr.deref e =>
    match step (fuel - 1) verbose config e with
    | some (config', e') => stepReturn fuel verbose (some (config', Expr.deref e'))
    | none => stepReturn fuel verbose none

  -- Rule: assign (assign value to location)
  -- --------------------------------------
  -- ⟨ l := n, m, r ⟩ → ⟨unit, m [ l |-> n ], r ⟩
  | Expr.assign (Expr.value (Value.loc l)) (Expr.value (Value.num n)) =>
    let config' := { config with memory := config.memory.update l n }
    stepReturn fuel verbose (some (config', Expr.unit))

  -- Rule: assign_eval_right (evaluate right side when left is a value)
  -- ⟨e2,m,r⟩ → ⟨e2',m',r'⟩
  -- --------------------------------------
  -- ⟨ l := e2, m, r ⟩ → ⟨ l := e2', m', r' ⟩
  | Expr.assign (Expr.value (Value.loc l)) e2 =>
    match step (fuel - 1) verbose config e2 with
    | some (config', e2') => stepReturn fuel verbose (some (config', Expr.assign (Expr.value (Value.loc l)) e2'))
    | none => stepReturn fuel verbose none

  -- Rule: assign_eval_left (evaluate left side of assignment)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- --------------------------------------
  -- ⟨ e1 := e2, m, r ⟩ → ⟨ e1' := e2, m', r' ⟩
  | Expr.assign e1 e2 =>
    match step (fuel - 1) verbose config e1 with
    | some (config', e1') => stepReturn fuel verbose (some (config', Expr.assign e1' e2))
    | none => stepReturn fuel verbose none

  -- Rule: seq1 (when first expression is a value, discard it and continue with second)
  -- --------------------------------------
  -- ⟨ v ; e, m, r ⟩ → ⟨ e, m, r ⟩
  | Expr.seq (Expr.value _v) e2 => stepReturn fuel verbose (some (config, e2))

  -- Rule: seq2 (evaluate first expression)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- --------------------------------------
  -- ⟨ e1 ; e2, m, r ⟩ → ⟨ e1' ; e2, m', r' ⟩
  | Expr.seq e1 e2 =>
    match step (fuel - 1) verbose config e1 with
    | some (config', e1') => stepReturn fuel verbose (some (config', Expr.seq e1' e2))
    | none => stepReturn fuel verbose none

  -- Rule: while (unfold to if-then-else)
  -- ---------------------------------------------------------------------------
  -- ⟨ while e1 do e2, m, r⟩ → ⟨ if e1 then ( e2 ; while e1 do e2 ) else unit, m, r ⟩
  | Expr.while e1 e2 =>
    let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.while e1 e2)) Expr.unit
    stepReturn fuel verbose (some (config, unfolded))

  -- Rule: let2 (substitute value)
  -- ---------------------------------------------------------------
  -- ⟨ let x : T = v in e2, m, r ⟩ → ⟨ e2, m, r[x |-> v] ⟩
  | Expr.let x _ (Expr.value v) e2 =>
    dbg_trace s!"let {x} = {v}";
    let config' := { config with varEnv := config.varEnv.update x v }
    stepReturn fuel verbose (some (config', e2))

  -- Rule: let1 (evaluate let binding)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- --------------------------------------------------------
  -- ⟨ let x : T = e1 in e2, m, r ⟩ → ⟨ let x : T = e1' in e2, m', r' ⟩
  | Expr.let x t e1 e2 =>
    match step (fuel - 1) verbose config e1 with
    | some (config', e1') => stepReturn fuel verbose (some (config', Expr.let x t e1' e2))
    | none => stepReturn fuel verbose none

  -- Rule: fn_abs (function abstraction creates closure)
  -- ---------------------------------------------------------------
  -- ⟨ fn x : T => e, m, r ⟩ → ⟨ closure(x, e, r), m, r ⟩
  | Expr.fn x _ body =>
    let closure := Value.closure x body config.varEnv
    stepReturn fuel verbose (some (config, closure.toExpr))

  -- Rule: pfn_abs (pure function abstraction creates pure closure)
  -- ---------------------------------------------------------------
  -- ⟨ pfn x : T => pe, m, r ⟩ → ⟨ pe_closure(x, pe, r), m, r ⟩
  | Expr.pfn x _ body =>
    let closure := Value.peClosure x body config.varEnv
    stepReturn fuel verbose (some (config, closure.toExpr))

  -- Function application rules
  | Expr.app (Expr.value (Value.closure x body env)) (Expr.value v)
  | Expr.app (Expr.value (Value.peClosure x body env)) (Expr.value v) =>
    -- Rule: app3/app3_pe (apply closure/pure closure to value)
    let config' := { config with varEnv := VarEnv.update env x v }
    let (config'', body') := eval (fuel-1) config' body verbose
    stepReturn fuel verbose (some ({config with memory := config''.memory}, body'))

  | Expr.app e1 (Expr.value v) =>
    match step (fuel - 1) verbose config e1 with
    | some (config', e1') => stepReturn fuel verbose (some (config', Expr.app e1' (Expr.value v)))
    | none => stepReturn fuel verbose none

  | Expr.app e1 e2 =>
    -- Rule: app1 (evaluate arguments)
    -- ⟨e2,m,r⟩ → ⟨e2',m',r'⟩
    -- ---------------------------------------------------------------
    -- ⟨ e1 e2, m, r ⟩ → ⟨ e1 e2', m', r' ⟩
    match step (fuel - 1) verbose config e2 with
    | some (config', e2') => stepReturn fuel verbose (some (config', Expr.app e1 e2'))
    | none => stepReturn fuel verbose none
termination_by fuel
-- Multi-step evaluation
def eval (fuel : Nat) (config : Config) (expr : Expr) (verbose : Bool) : (Config × Expr) :=
  if fuel < 2 then
    (config, expr)
  else
    match step (fuel - 1) verbose config expr with
    | some (config', expr') =>
      eval (fuel - 2) config' expr' verbose
    | none =>
      (config, expr)
termination_by fuel

end -- mutual (step, eval)

-- Helper to run an expression with empty environments
def run (fuel : Nat) (expr : Expr) (verbose : Bool := false) : (Config × Expr) :=
  let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0⟩
  eval fuel initialConfig expr verbose

-- Default fuel amount
def defaultFuel : Nat := 1000
