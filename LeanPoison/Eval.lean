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
def step (fuel : Nat) (verbose : Bool) (config : Config) (expr : Expr) : IO (Option (Config × Expr)) :=
  do
  let _ := stepEntryTrace fuel verbose config expr
  if fuel = 0 then
    dbg_trace s!"out of fuel";
    return stepReturn fuel verbose none
  else
    match expr with
  -- Values are stuck (cannot reduce)
  | Expr.value _ => return stepReturn fuel verbose none

  -- Rule: var
  -- r(x) = v
  -- ------------------------
  -- ⟨ x, m, r ⟩ → ⟨ v, m, r ⟩
  | Expr.var x =>
    match config.varEnv x with
    | some v => return stepReturn fuel verbose (some (config, v.toExpr))
    | none =>
      dbg_trace s!"var {x} not found";
      return stepReturn fuel verbose none

  -- Rule: op_plus and op_gteq (when both operands are values)
  -- n1 + n2 = n
  -- ------------------------
  -- ⟨n1 + n2, m, r⟩ → ⟨n, m, r⟩
  | Expr.op (Expr.value v1) op (Expr.value v2) =>
    match evalOp op v1 v2 with
    | some v => return stepReturn fuel verbose (some (config, v.toExpr))
    | none => return stepReturn fuel verbose none

  -- Rule: op2 (evaluate right operand when left is a value)
  -- ⟨e2,m,r⟩ → ⟨e2',m',r'⟩
  -- -------------------------------
  -- ⟨v1 op e2,m,r⟩ → ⟨v1 op e2',m',r'⟩
  | Expr.op (Expr.value v1) op e2 =>
    match (<- step (fuel - 1) verbose config e2) with
    |  some (config', e2') => return stepReturn fuel verbose (some (config', Expr.op (Expr.value v1) op e2'))
    | none =>return stepReturn fuel verbose none

  -- Rule: op1 (evaluate left operand first)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- -------------------------------
  -- ⟨e1 op e2,m,r⟩ → ⟨e1' op e2,m',r'⟩
  | Expr.op e1 op e2 =>
    match <- step (fuel - 1) verbose config e1 with
    | some (config', e1') => return stepReturn fuel verbose (some (config', Expr.op e1' op e2))
    | none => return stepReturn fuel verbose none

  -- Rule: if1, if2, if3
  -- --------------------------------
  -- ⟨ if true then e1 else e2, m, r ⟩ → ⟨ e1, m, r ⟩
  -- ⟨ if false then e1 else e2, m, r ⟩ → ⟨ e2, m, r ⟩
  | Expr.ite (Expr.value (Value.bool true)) e2 _e3 => return stepReturn fuel verbose (some (config, e2))
  | Expr.ite (Expr.value (Value.bool false)) _e2 e3 => return stepReturn fuel verbose (some (config, e3))
  | Expr.ite e1 e2 e3 =>
    -- Rule: if3 (evaluate condition)
    -- ⟨e,m,r⟩ → ⟨e',m',r'⟩
    -- ------------------------------------------------------------
    -- ⟨ if e then e1 else e2, m, r ⟩ → ⟨ if e' then e1 else e2, m', r' ⟩
       match <- step (fuel - 1) verbose config e1 with
    | some (config', e1') => return stepReturn fuel verbose (some (config', Expr.ite e1' e2 e3))
    | none => return stepReturn fuel verbose none

  -- Rule: ref (allocate new reference when argument is a value)
  -- fresh l
  -- ------------------------------
  -- ⟨ref n,m,r⟩ → ⟨l, m [ l |-> n ], r⟩
  | Expr.newRef (Expr.value (Value.num n)) =>
    let (l, config') := freshLoc config
    let config'' := { config' with memory := config'.memory.update l n }
    return stepReturn fuel verbose (some (config'', Expr.loc l))

  -- Rule: ref_eval (evaluate argument of ref)
  -- ⟨e,m,r⟩ → ⟨e',m',r'⟩
  -- ------------------------------
  -- ⟨ref e,m,r⟩ → ⟨ref e',m',r'⟩
  | Expr.newRef e =>
    match <- step (fuel - 1) verbose config e with
    | some (config', e') => return  stepReturn fuel verbose (some (config', Expr.newRef e'))
    | none => return  stepReturn fuel verbose none

  -- Rule: deref_loc (dereference a location)
  -- m(l) = n
  -- ------------------------------
  -- ⟨!l,m,r⟩ → ⟨n,m,r⟩
  | Expr.deref (Expr.value (Value.loc l)) =>
    match config.memory.get? l with
    | some n => return stepReturn fuel verbose (some (config, Expr.num n))
    | none =>
      dbg_trace s!"deref {l} not found";
      -- Dereferencing a location that is not in the memory returns default value 0
      -- this is an example of poisoned value
      return stepReturn fuel verbose (some (config, Expr.num 0))

  -- Rule: deref_eval (evaluate argument of deref)
  -- ⟨e,m,r⟩ → ⟨e',m',r'⟩
  -- ------------------------------
  -- ⟨!e,m,r⟩ → ⟨!e',m',r'⟩
  | Expr.deref e =>
    match <- step (fuel - 1) verbose config e with
    | some (config', e') => return stepReturn fuel verbose (some (config', Expr.deref e'))
    | none => return stepReturn fuel verbose none

  -- Rule: assign (assign value to location)
  -- --------------------------------------
  -- ⟨ l := n, m, r ⟩ → ⟨unit, m [ l |-> n ], r ⟩
  | Expr.assign (Expr.value (Value.loc l)) (Expr.value (Value.num n)) =>
    let config' := { config with memory := config.memory.update l n }
    return stepReturn fuel verbose (some (config', Expr.unit))

  -- Rule: assign_eval_right (evaluate right side when left is a value)
  -- ⟨e2,m,r⟩ → ⟨e2',m',r'⟩
  -- --------------------------------------
  -- ⟨ l := e2, m, r ⟩ → ⟨ l := e2', m', r' ⟩
  | Expr.assign (Expr.value (Value.loc l)) e2 =>
    match <- step (fuel - 1) verbose config e2 with
    | some (config', e2') => return  stepReturn fuel verbose (some (config', Expr.assign (Expr.value (Value.loc l)) e2'))
    | none =>return stepReturn fuel verbose none

  -- Rule: assign_eval_left (evaluate left side of assignment)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- --------------------------------------
  -- ⟨ e1 := e2, m, r ⟩ → ⟨ e1' := e2, m', r' ⟩
  | Expr.assign e1 e2 =>
    match <- step (fuel - 1) verbose config e1 with
    | some (config', e1') => return stepReturn fuel verbose (some (config', Expr.assign e1' e2))
    | none => return stepReturn fuel verbose none

  -- Rule: seq1 (when first expression is a value, discard it and continue with second)
  -- --------------------------------------
  -- ⟨ v ; e, m, r ⟩ → ⟨ e, m, r ⟩
  | Expr.seq (Expr.value _v) e2 => return stepReturn fuel verbose (some (config, e2))

  -- Rule: seq2 (evaluate first expression)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- --------------------------------------
  -- ⟨ e1 ; e2, m, r ⟩ → ⟨ e1' ; e2, m', r' ⟩
  | Expr.seq e1 e2 =>
    match <- step (fuel - 1) verbose config e1 with
    | some (config', e1') => return stepReturn fuel verbose (some (config', Expr.seq e1' e2))
    | none => return stepReturn fuel verbose none

  -- Rule: while (unfold to if-then-else)
  -- ---------------------------------------------------------------------------
  -- ⟨ while e1 do e2, m, r⟩ → ⟨ if e1 then ( e2 ; while e1 do e2 ) else unit, m, r ⟩
  | Expr.while e1 e2 =>
    let unfolded := Expr.ite e1 (Expr.seq e2 (Expr.while e1 e2)) Expr.unit
    return stepReturn fuel verbose (some (config, unfolded))

  -- Rule: let2 (substitute value)
  -- ---------------------------------------------------------------
  -- ⟨ let x = v in e2, m, r ⟩ → ⟨ e2, m, r[x |-> v] ⟩
  | Expr.let x (Expr.value v) e2 =>
   --dbg_trace s!"let {x} = {v}";
    let config' := { config with varEnv := config.varEnv.update x v }
    return stepReturn fuel verbose (some (config', e2))

  -- Rule: let1 (evaluate let binding)
  -- ⟨e1,m,r⟩ → ⟨e1',m',r'⟩
  -- --------------------------------------------------------
  -- ⟨ let x = e1 in e2, m, r ⟩ → ⟨ let x = e1' in e2, m', r' ⟩
  | Expr.let x e1 e2 =>
    match <- step (fuel - 1) verbose config e1 with
    | some (config', e1') => return stepReturn fuel verbose (some (config', Expr.let x e1' e2))
    | none => return stepReturn fuel verbose none

  -- Rule: fn_abs (function abstraction creates closure)
  -- ---------------------------------------------------------------
  -- ⟨ fn x : T => e, m, r ⟩ → ⟨ closure(x, e, r), m, r ⟩
  | Expr.fn x _paramType body _returnType =>
    let closure := Value.closure x body config.varEnv
    return stepReturn fuel verbose (some (config, closure.toExpr))

  -- Rule: pfn_abs (pure function abstraction creates pure closure)
  -- ---------------------------------------------------------------
  -- ⟨ pfn x : T => pe, m, r ⟩ → ⟨ pe_closure(x, pe, r), m, r ⟩
  | Expr.pfn x _paramType body _returnType =>
    let closure := Value.peClosure x body config.varEnv
    return stepReturn fuel verbose (some (config, closure.toExpr))

  -- Function application rules
  | Expr.app (Expr.value (Value.closure x body env)) (Expr.value v)
  | Expr.app (Expr.value (Value.peClosure x body env)) (Expr.value v) =>
    -- Rule: app3/app3_pe (apply closure/pure closure to value)
    let config' := { config with varEnv := VarEnv.update env x v }
    let (config'', body') <- eval (fuel-1) config' body verbose
    return stepReturn fuel verbose (some ({config with memory := config''.memory}, body'))

  | Expr.app e1 (Expr.value v) =>
    match <- step (fuel - 1) verbose config e1 with
    | some (config', e1') => return stepReturn fuel verbose (some (config', Expr.app e1' (Expr.value v)))
    | none => return stepReturn fuel verbose none

  | Expr.app e1 e2 =>
    -- Rule: app1 (evaluate arguments)
    -- ⟨e2,m,r⟩ → ⟨e2',m',r'⟩
    -- ---------------------------------------------------------------
    -- ⟨ e1 e2, m, r ⟩ → ⟨ e1 e2', m', r' ⟩
    match <- step (fuel - 1) verbose config e2 with
    | some (config', e2') => return stepReturn fuel verbose (some (config', Expr.app e1 e2'))
    | none => return stepReturn fuel verbose none
   ----------------------------------------------------------------------------
       -- Rule:rand arg
        --       < e, µ, ρ > → < e′, µ′, ρ′ >
        --  -------------------------------------------
        -- < rand e, µ, ρ > → < rand e′, µ′, ρ′ >

  | Expr.builtIn (builtInExpr.rand (Expr.value (Value.num n))) =>
     if n >= 0 then
       do
        let r <- (IO.rand 0 n.toNat).toIO   -- r : Nat
        let randomNo := Int.ofNat r  -- convert Nat to Int
        return stepReturn fuel verbose (some (config , Expr.value (Value.num randomNo)))
     else
      IO.println "Argument to rand must evaluate to non negative integer"
      return stepReturn fuel verbose none


  | Expr.builtIn (builtInExpr.rand e) =>
    match <- step (fuel - 1) verbose config e with
    | some (config',e') => return stepReturn fuel verbose (some (config',Expr.builtIn (builtInExpr.rand e')))
    | none => return stepReturn fuel verbose none

   ---------------------------------------------------------------------------
     -- Rule:frand arg```
      --      < e, µ, ρ > → < e′, µ′, ρ′ >
      --   -------------------------------------------
      --     < frand e, µ, ρ > → < frand e′, µ′, ρ′ >

  | Expr.builtIn (builtInExpr.frand (Expr.value (Value.num n))) =>
     if n >= 0 then
      do
        let maxRange : Nat := 4 * (n.toNat)
        let r <- (IO.rand 0 maxRange).toIO   --   0 <= r <= 4n
        let randomNo : Int := (Int.ofNat r) - (2 * n)  --  -2n <= randomNo <= 2n
        return stepReturn fuel verbose (some (config , Expr.value (Value.num randomNo)))
      else
        IO.println "Argument to frand must evaluate to non negative integer"
        return stepReturn fuel verbose none


  | Expr.builtIn (builtInExpr.frand e) =>
    match <- step (fuel - 1) verbose config e with
    | some (config',e') => return stepReturn fuel verbose (some (config',Expr.builtIn (builtInExpr.frand e')))
    | none => return stepReturn fuel verbose none
----------------------------------------------------------------------------------------
termination_by fuel
----------------------------------------------------------------------------------------
-- Multi-step evaluation
def eval (fuel : Nat) (config : Config) (expr : Expr) (verbose : Bool) : IO (Config × Expr) := do
  if fuel < 2 then
    return (config, expr)
  else
    match <- step (fuel - 1) verbose config expr with
    | some (config', expr') =>
      eval (fuel - 2) config' expr' verbose
    | none =>
      return (config, expr)
termination_by fuel

end -- mutual (step, eval)

-- Helper to run an expression with empty environments
def run (fuel : Nat) (expr : Expr) (verbose : Bool := false) : IO (Config × Expr) :=
  let initialConfig : Config := ⟨emptyMemory, emptyVarEnv, 0⟩
  eval fuel initialConfig expr verbose
