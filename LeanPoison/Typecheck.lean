import LeanPoison.Syntax
import LeanPoison.Poison
import Std.Data.HashMap
open Std

-- Type checking environment definitions

/-- Memory typing environment (Γ in the Ott spec) -/
abbrev MemoryTypeEnv := HashMap Address QTyp

/-- Tag valuation environment (ℒ in the Ott spec) -/
abbrev TagEnv := HashMap Tag Bool

/-- Type checking context containing all environments -/
structure TypeContext where
  pc : Poison            -- Poison context
  memEnv : MemoryTypeEnv -- Γ
  varEnv : VarTypeEnv    -- σ
  tagEnv : TagEnv        -- ℒ

/-- Type checking result: qualified type and updated memory environment -/
structure TypeResult where
  qualType : QTyp
  memEnv' : MemoryTypeEnv
  tagEnv' : TagEnv  -- Updated logical environment

/-- Type checking monad for error handling -/
abbrev TypecheckM := Except String

-- Helper functions

/-- Join two poison flags -/
def joinPoison (p1 p2 : Poison) : Poison :=
  p1 || p2

/-- Join multiple poison flags -/
def joinPoisons (ps : List Poison) : Poison :=
  ps.foldl joinPoison false

/-- Update memory environment at a location -/
def updateMemEnv (env : MemoryTypeEnv) (l : Address) (qt : QTyp) : MemoryTypeEnv :=
  env.insert l qt

/-- Update variable environment -/
def updateVarEnv (env : VarTypeEnv) (x : Name) (qt : QTyp) : VarTypeEnv :=
  fun y => if y == x then some qt else env y

/-- Join two memory environments (for conditional branches) -/
def joinMemEnvs (env1 env2 : MemoryTypeEnv) : MemoryTypeEnv :=
  -- For now, return union preferring env2 for conflicts
  -- TODO: Implement proper join operation as per Ott spec
  env1.fold (init := env2) fun acc l qt => acc.insert l qt

/-- Fresh location generation -/
-- TODO: why unused?
def freshLocation : StateM Nat Address := do
  let l ← get
  modify (· + 1)
  return l

/-- Fresh tag generation -/
-- TODO: why unused?
def freshTag : StateM Nat Tag := do
  let k ← get
  modify (· + 1)
  return k

/-- Match guard function (simplified implementation) -/
def matchGuard (_e : Expr) (_G : MemoryTypeEnv) (_S : VarTypeEnv) : Option Tag :=
  -- TODO: Implement proper match_guard logic
  -- For now, return none (no matching predicate found)
  none

-- Manual BEq instance for PTyp (needed for type checking)
mutual
def beqPTyp : PTyp → PTyp → Bool
  | PTyp.int, PTyp.int => true
  | PTyp.bool, PTyp.bool => true
  | PTyp.unit, PTyp.unit => true
  | PTyp.ref t1 l1, PTyp.ref t2 l2 => beqPTyp t1 t2 && l1 == l2
  | PTyp.arrow t1 t2 p1 tcl1, PTyp.arrow t3 t4 p2 tcl2 =>
    beqPTyp t1 t3 && beqPTyp t2 t4 && p1 == p2 && beqTClosure tcl1 tcl2
  | _, _ => false

def beqTClosure : TClosure → TClosure → Bool
  | TClosure.fn_tclosure x1 _ _, TClosure.fn_tclosure x2 _ _ => x1 == x2
  | TClosure.pfn_tclosure x1 _ _, TClosure.pfn_tclosure x2 _ _ => x1 == x2
  | _, _ => false
end

instance : BEq PTyp where
  beq := beqPTyp

instance : BEq TClosure where
  beq := beqTClosure

-- Helper function to convert Expr to PExpr
def Expr.toPExpr (e : Expr) : TypecheckM PExpr :=
  match e with
  | Expr.value v => return PExpr.value v
  | Expr.var x => return PExpr.var x
  | Expr.op e1 opname e2 => do
    let pe1 ← e1.toPExpr
    let pe2 ← e2.toPExpr
    return PExpr.op pe1 opname pe2
  | Expr.ite e1 e2 e3 => do
    let pe1 ← e1.toPExpr
    let pe2 ← e2.toPExpr
    let pe3 ← e3.toPExpr
    return PExpr.ite pe1 pe2 pe3
  | Expr.deref e => do
    let pe ← e.toPExpr
    return PExpr.deref pe
  | Expr.seq e1 e2 => do
    let pe1 ← e1.toPExpr
    let pe2 ← e2.toPExpr
    return PExpr.seq pe1 pe2
  | Expr.let x e1 e2 => do
    let pe1 ← e1.toPExpr
    let pe2 ← e2.toPExpr
    return PExpr.let x pe1 pe2
  | Expr.app e1 e2 => do
    let pe1 ← e1.toPExpr
    let pe2 ← e2.toPExpr
    return PExpr.app pe1 pe2
  | _ => throw "Cannot convert expression to PExpr"

-- Helper function to convert PTyp to Typ
def PTyp.toTyp (pt : PTyp) : Typ :=
  match pt with
  | PTyp.int => Typ.int
  | PTyp.bool => Typ.bool
  | PTyp.unit => Typ.unit
  | PTyp.ref t _ => Typ.ref (toTyp t)
  | PTyp.arrow t1 t2 _ _ => Typ.arrow (toTyp t1) (toTyp t2)

-- Helper function to convert PExpr to Expr
def PExpr.toExpr (pe : PExpr) : Expr :=
  match pe with
  | PExpr.value v => Expr.value v
  | PExpr.var x => Expr.var x
  | PExpr.op e1 o e2 => Expr.op (e1.toExpr) o (e2.toExpr)
  | PExpr.ite e1 e2 e3 => Expr.ite (e1.toExpr) (e2.toExpr) (e3.toExpr)
  | PExpr.deref e => Expr.deref (e.toExpr)
  | PExpr.seq e1 e2 => Expr.seq (e1.toExpr) (e2.toExpr)
  | PExpr.let x e1 e2 => Expr.let x (e1.toExpr) (e2.toExpr)
  | PExpr.app e1 e2 => Expr.app (e1.toExpr) (e2.toExpr)



-- Type checking rules implementation

/-- Rule: int (Ott rule: int)
-- pc ; G ; S ; L |- n : int :> clean { no_pred } -| G ; L
-/
def typecheckInt (ctx : TypeContext) (_n : Nat) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨PTyp.int, false, none⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }

/-- Rule: bool (Ott rule: bool)
-- pc ; G ; S ; L |- b : bool :> clean { no_pred } -| G ; L
-/
def typecheckBool (ctx : TypeContext) (_b : Bool) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨PTyp.bool, false, none ⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }


/-- Rule: var_no_pred (Ott rule: var_no_pred)
-- S(x) = T :> p { no_pred }
-- ------------------
-- pc ; G ; S ; L |- x : T :> join pc p { no_pred } -| G ; L
-/
def typecheckVarNoPred (ctx : TypeContext) (x : Name) : TypecheckM TypeResult := do
  match ctx.varEnv x with
  | some qt =>
    match qt with
    | ⟨ptyp, poison, pred⟩ =>
    match pred with
    | none =>  -- no_pred case
      let poison := joinPoison ctx.pc poison
      let qt' : QTyp := ⟨ptyp, poison, none ⟩
      return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
    | some tp =>  -- has predicate
      let ⟨k, tcl ⟩:= tp
      match ctx.tagEnv.get? k with
      | some true =>  -- guard_true case
        let qt' : QTyp := ⟨ptyp, ctx.pc, none ⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
      | some false =>  -- guard_false case
        let qt' : QTyp := ⟨ptyp, true, none ⟩  -- poisoned
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
      | none =>  -- guard_unknown case
        let poison := joinPoison ctx.pc poison
        let tp' : TPred := ⟨k, tcl ⟩
        let qt' : QTyp := ⟨ptyp, poison, some tp' ⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
  | none => throw s!"Variable {x} not found in environment"


/-- Rule: location (Ott rule: location)
-- G(l) = T :> p { P }
-- ------------------
-- pc ; G ; S ; L |- l : ref T @ l :> clean { no_pred } -| G ; L
-/
def typecheckLocation (ctx : TypeContext) (l : Address) : TypecheckM TypeResult := do
  match ctx.memEnv.get? l with
  | some qt =>
    let ⟨ptyp, _p, pred ⟩ := qt
    let refTyp := PTyp.ref ptyp l
    let qt' : QTyp := ⟨refTyp, false, pred ⟩  -- clean, no predicate
    return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
  | none => throw s!"Location {l} not found in memory environment"

/-- Rule: unit (Ott rule: unit)
-- pc ; G ; S ; L |- unit : unit :> clean { no_pred } -| G ; L
-/
def typecheckUnit (ctx : TypeContext) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨PTyp.unit, false, none  ⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }


/--
  For any n ≠ 0, `n.pred < n`.
  (Lean’s `termination_by` always gives you `h : n ≠ 0` in the context,
   so this lines up perfectly.)
-/
theorem Nat.pred_lt_of_ne_zero {n : Nat} (h : n ≠ 0) : n - 1 < n := by
  cases n
  · contradiction
  · apply Nat.lt_succ_self



/-
mutual

def foo(n : Nat) : Except String Nat :=
  if n = 0 then return 0 else bar (n - 1)

def bar(n : Nat) : Except String Nat :=
  if n = 0 then return 0 else do
    let x ← foo (n - 1)
    return x + 1

end
-/


set_option maxHeartbeats 400000

mutual

-- Helper function to type check an expression with context
def typecheckExpr (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    match e with
    | Expr.value (Value.num n) => typecheckInt ctx n
    | Expr.value (Value.bool b) => typecheckBool ctx b
    | Expr.value Value.unit => typecheckUnit ctx
    | Expr.value (Value.loc l) => typecheckLocation ctx l
    | Expr.value _ => throw "Unsupported value type"
    | Expr.var x => typecheckVarNoPred ctx x
    | Expr.op e1 Op.add e2 => typecheckOpPlus ctx e1 e2 (fuel - 1)
    | Expr.op e1 Op.gte e2 => typecheckOpGte ctx e1 e2 (fuel - 1)
    | Expr.newRef e => typecheckNewRef ctx e (fuel - 1)
    | Expr.assign e1 e2 => typecheckAssign ctx e1 e2 (fuel - 1)
    | Expr.deref e => typecheckDeref ctx e (fuel - 1)
    | Expr.seq e1 e2 => typecheckSeq ctx e1 e2 (fuel - 1)
    | Expr.while e1 e2 => typecheckWhile ctx e1 e2 (fuel - 1)
    | Expr.let x e1 e2 => typecheckLet ctx x e1 e2 (fuel - 1)
    | Expr.fn x body => typecheckFn ctx x body (fuel - 1)
    | Expr.pfn x body => typecheckPfn ctx x body (fuel - 1)
    | Expr.app e1 e2 => typecheckApp ctx e1 e2 (fuel - 1)
    | Expr.ite e1 e2 e3 => typecheckIf ctx e1 e2 e3 (fuel - 1)
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›



/-- Rule: op_plus (Ott rule: op_plus)
-- pc ; G ; S ; L |- e1 : int :> p' { P1 } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : int :> p'' { P2 } -| G'' ; L''
-- --------------------------------
-- pc ; G ; S ; L |- e1 + e2 : int :> join pc join p' p'' { no_pred } -| G'' ; L''
-/
def typecheckOpPlus (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p1, _  ⟩ := result1.qualType
    if ptyp1 != PTyp.int then throw "Left operand of + must be int"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
    let result2 ← typecheckExpr ctx' e2 (fuel - 1)
    let ⟨ptyp2, p2, _  ⟩ := result2.qualType
    if ptyp2 != PTyp.int then throw "Right operand of + must be int"

    let poison := joinPoison ctx.pc (joinPoison p1 p2)
    let qt : QTyp := ⟨PTyp.int, poison, none  ⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv' }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: op_gteq (Ott rule: op_gteq)
-- pc ; G ; S ; L |- e1 : int :> p' { P1 } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : int :> p'' { P2 } -| G'' ; L''
-- --------------------------------
-- pc ; G ; S ; L |- e1 >= e2 : bool :> join pc join p' p'' { no_pred } -| G'' ; L''
-/
def typecheckOpGte (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p1, _  ⟩ := result1.qualType
    if ptyp1 != PTyp.int then throw "Left operand of >= must be int"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
    let result2 ← typecheckExpr ctx' e2 (fuel - 1)
    let ⟨ptyp2, p2, _  ⟩ := result2.qualType
    if ptyp2 != PTyp.int then throw "Right operand of >= must be int"

    let poison := joinPoison ctx.pc (joinPoison p1 p2)
    let qt : QTyp := ⟨PTyp.bool, poison, none  ⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv' }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: ref (Ott rule: ref)
-- pc ; G ; S ; L |- e : T :> p { P } -| G' ; L'
-- fresh l
-- -----------------------
-- pc ; G ; S ; L |- ref e : ref T @ l :> pc { no_pred } -| G'[l |-> T :> join pc p { P }] ; L'
-/
def typecheckNewRef (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result ← typecheckExpr ctx e (fuel - 1)
    let ⟨ptyp, poison, pred ⟩ := result.qualType

    -- Generate fresh location (simplified)
    let l := ctx.memEnv.size
    let refTyp := PTyp.ref ptyp l
    let storedPoison := joinPoison ctx.pc poison
    let storedQt : QTyp := ⟨refTyp, storedPoison, pred  ⟩
    let memEnv' := updateMemEnv result.memEnv' l storedQt

    let qt : QTyp := ⟨refTyp, ctx.pc, none  ⟩
    return { qualType := qt, memEnv' := memEnv', tagEnv' := result.tagEnv' }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: assign (Ott rule: assign)
-- pc ; G ; S ; L |- e1 : ref T @ l :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T :> p'' { P'' } -| G'' ; L''
-- -----------------------
-- pc ; G ; S ; L |- e1 := e2 : unit :> join pc p' { no_pred } -| G''[l |-> T :> join pc join p' p'' { P'' }] ; L''
-/
def typecheckAssign (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p1, _  ⟩ := result1.qualType
    match ptyp1 with
    | PTyp.ref t l =>
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
      let result2 ← typecheckExpr ctx' e2 (fuel - 1)
      let ⟨ptyp2, p2, pred2  ⟩ := result2.qualType
      if ptyp2 != t then throw "Type mismatch in assignment"

      let storedPoison := joinPoison ctx.pc (joinPoison p1 p2)
      let storedQt : QTyp := ⟨t, storedPoison, pred2  ⟩
      let memEnv' := updateMemEnv result2.memEnv' l storedQt

      let resultPoison := joinPoison ctx.pc p1
      let qt : QTyp := ⟨PTyp.unit, resultPoison, none  ⟩
      return { qualType := qt, memEnv' := memEnv', tagEnv' := result2.tagEnv' }
    | _ => throw "Left operand of assignment must be a reference"
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: deref_no_pred (Ott rule: deref_no_pred)
-- pc ; G ; S ; L |- e : ref T @ l :> p' { P' } -| G' ; L'
-- G'(l) = T :> p { no_pred }
-- -----------------------
-- pc ; G ; S ; L |- !e : T :> join pc join p' p { no_pred } -| G' ; L'
-/
def typecheckDeref (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result ← typecheckExpr ctx e (fuel - 1)
    let ⟨ptyp, poison, _pred ⟩ := result.qualType
    match ptyp with
    | PTyp.ref t l =>
      match result.memEnv'.get? l with
      | some ⟨ptyp', p2, none ⟩ =>  -- no_pred case
        if ptyp' != t then throw "Type mismatch in dereference"
        let poison := joinPoison ctx.pc (joinPoison poison p2)
        let qt : QTyp := ⟨t, poison, none  ⟩
        return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv' }
      | some ⟨ptyp', p2, some ⟨k, tcl ⟩ ⟩ =>  -- has predicate
        if ptyp' != t then throw "Type mismatch in dereference"
        match result.tagEnv'.get? k with
        | some true =>  -- guard_true case
          let poison := joinPoison ctx.pc poison
          let qt : QTyp := ⟨t, poison, none  ⟩
          return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv' }
        | some false =>  -- guard_false case
          let qt : QTyp := ⟨t, true, none  ⟩  -- poisoned
          return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv' }
        | none =>  -- guard_unknown case
          let poison := joinPoison ctx.pc (joinPoison poison p2)
          let qt : QTyp := ⟨t, poison, some ⟨k, tcl ⟩ ⟩
          return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv' }
      | none => throw s!"Location {l} not found in memory environment"
    | _ => throw "Operand of dereference must be a reference"
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: seq (Ott rule: seq)
-- pc ; G ; S ; L |- e1 : T1 :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T2 :> p'' { P'' } -| G'' ; L''
-- --------------------------------
-- pc ; G ; S ; L |- e1 ; e2 : T2 :> join p' p'' { P'' } -| G'' ; L''
-/
def typecheckSeq (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨_ptyp1, p1, _  ⟩ := result1.qualType

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
    let result2 ← typecheckExpr ctx' e2 (fuel - 1)
    let ⟨ptyp2, p2, pred2  ⟩ := result2.qualType

    let poison := joinPoison p1 p2
    let qt : QTyp := ⟨ptyp2, poison, pred2  ⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv' }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: fn_abs (Ott rule: fn_abs)
-- pc ; G ; S[x |-> T1 :> pc { no_pred }] ; L |- e : T2 :> p' { P' } -| G' ; L'
-- ----------------------------------------------------------------------
-- pc ; G ; S ; L |- fn x : T1 => e : T1 -> T2 # pc typing_closure ( x , e , S ) :> pc { no_pred } -| G' ; L
-/
def typecheckFn (ctx : TypeContext) (x : Name) (body : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    -- For type inference, we need to infer the parameter type from usage
    -- For now, use a placeholder type - proper type inference would require more complex logic
    let t1' := PTyp.int  -- Placeholder type

    let varQt : QTyp := ⟨t1', ctx.pc, none  ⟩
    let varEnv' := updateVarEnv ctx.varEnv x varQt
    let ctx' := { ctx with varEnv := varEnv' }

    let result ← typecheckExpr ctx' body (fuel - 1)
    let ⟨ptyp2, _p', _pred'  ⟩ := result.qualType

    let tcl := TClosure.fn_tclosure x body ctx.varEnv
    let arrowTyp := PTyp.arrow t1' ptyp2 ctx.pc tcl
    let qt : QTyp := ⟨arrowTyp, ctx.pc, none  ⟩
    return { qualType := qt, memEnv' := result.memEnv', tagEnv' := ctx.tagEnv }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: pfn_abs (Ott rule: pfn_abs)
-- pc ; G ; S[x |-> T1 :> pc { no_pred }] ; L |- pe : T2 :> p' { P' } -| G' ; L'
-- ----------------------------------------------------------------------
-- pc ; G ; S ; L |- pfn x : T1 => pe : T1 -> T2 # pc typing_closure ( x , pe , S ) :> pc { no_pred } -| G' ; L
-/
def typecheckPfn (ctx : TypeContext) (x : Name) (body : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    -- For type inference, we need to infer the parameter type from usage
    -- For now, use a placeholder type - proper type inference would require more complex logic
    let t1' := PTyp.int  -- Placeholder type

    let varQt : QTyp := ⟨t1', ctx.pc, none  ⟩
    let varEnv' := updateVarEnv ctx.varEnv x varQt
    let ctx' := { ctx with varEnv := varEnv' }

    let result ← typecheckExpr ctx' body (fuel - 1)
    let ⟨ptyp2, _p', _pred'  ⟩ := result.qualType

    let pbody ← body.toPExpr
    let tcl := TClosure.pfn_tclosure x pbody ctx.varEnv
    let arrowTyp := PTyp.arrow t1' ptyp2 ctx.pc tcl
    let qt : QTyp := ⟨arrowTyp, ctx.pc, none  ⟩
    return { qualType := qt, memEnv' := result.memEnv', tagEnv' := ctx.tagEnv }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: app_fn (Ott rule: app_fn)
-- pc ; G ; S ; L |- e1 : T1 -> T2 # p typing_closure ( x , e , S' ) :> p1 { P1 } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
-- pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- e : T2 :> p3 { P3 } -| G''' ; L'''
-- ----------------------------------------------------------------------
-- pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''
-/
def typecheckApp (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, _p1, _  ⟩ := result1.qualType
    match ptyp1 with
    | PTyp.arrow t1 _t2 _p tcl =>
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
      let result2 ← typecheckExpr ctx' e2 (fuel - 1)
      let ⟨ptyp2, p2, pred2  ⟩ := result2.qualType
      if ptyp2 != t1 then throw "Type mismatch in function application"

      match tcl with
      | TClosure.fn_tclosure x body env =>
        let argQt : QTyp := ⟨t1, joinPoison ctx.pc p2, pred2  ⟩
        let env' := updateVarEnv env x argQt
        let ctx'' := { ctx with memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv' }
        let result3 ← typecheckExpr ctx'' body (fuel - 1)
        let ⟨ptyp3, p3, pred3  ⟩ := result3.qualType

        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨ptyp3, poison, pred3  ⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv' }
      | TClosure.pfn_tclosure x body env =>
        let argQt : QTyp := ⟨t1, joinPoison ctx.pc p2, pred2  ⟩
        let env' := updateVarEnv env x argQt
        let ctx'' := { ctx with memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv' }
        let result3 ← typecheckExpr ctx'' (body.toExpr) (fuel - 1)
        let ⟨ptyp3, p3, pred3  ⟩ := result3.qualType

        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨ptyp3, poison, pred3  ⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv' }
    | _ => throw "Left operand of application must be a function"
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: let (Ott rule: let)
-- pc ; G ; S ; L |- e1 : T :> p1 { P1 } -| G' ; L'
-- pc ; G' ; S[x |-> T :> join pc p1 { P1 }] ; L' |- e2 : T2 :> p2 { P2 } -| G'' ; L''
-- ----------------------------------------------------------------------
-- pc ; G ; S ; L |- let x : T = e1 in e2 : T2 :> join pc join p1 p2 { P2 } -| G'' ; L''
-/
def typecheckLet (ctx : TypeContext) (x : Name) (e1 : Expr) (e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p1, pred1  ⟩ := result1.qualType

    let varPoison := joinPoison ctx.pc p1
    let varQt : QTyp := ⟨ptyp1, varPoison, pred1  ⟩
    let varEnv' := updateVarEnv ctx.varEnv x varQt
    let ctx' := { ctx with memEnv := result1.memEnv', varEnv := varEnv', tagEnv := result1.tagEnv' }

    let result2 ← typecheckExpr ctx' e2 (fuel - 1)
    let ⟨ptyp2, p2, pred2  ⟩ := result2.qualType

    let poison := joinPoison ctx.pc (joinPoison p1 p2)
    let qt : QTyp := ⟨ptyp2, poison, pred2  ⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv' }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: if_std (Ott rule: if_std - standard conditional when no matching predicate found)
-- pc ; G ; S ; L |- e1 : bool :> p' { P' } -| G' ; L'
-- join pc p' ; G' ; S ; L' |- e2 : T :> p'' { P'' } -| G'' ; L''
-- join pc p' ; G' ; S ; L' |- e3 : T :> p''' { P''' } -| G''' ; L'''
-- ----------------------------------
-- pc ; G ; S ; L |- if e1 then e2 else e3 : T :> join pc join p' join p'' p''' { no_pred } -| JoinG G'' G''' ; L'
-/
def typecheckIf (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p', _  ⟩ := result1.qualType
    if ptyp1 != PTyp.bool then throw "Condition of if must be bool"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
    let branchPc := joinPoison ctx.pc p'
    let ctx'' := { ctx' with pc := branchPc }

    let result2 ← typecheckExpr ctx'' e2 (fuel - 1)
    let ⟨ptyp2, p'', _  ⟩ := result2.qualType

    let result3 ← typecheckExpr ctx'' e3 (fuel - 1)
    let ⟨ptyp3, p''', _  ⟩ := result3.qualType

    if ptyp2 != ptyp3 then throw "Branches of if must have same type"

    let poison := joinPoison ctx.pc (joinPoison p' (joinPoison p'' p'''))
    let qt : QTyp := ⟨ptyp2, poison, none  ⟩
    let memEnv' := joinMemEnvs result2.memEnv' result3.memEnv'
    return { qualType := qt, memEnv' := memEnv', tagEnv' := ctx'.tagEnv }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: while_std (Ott rule: while_std - standard while when no matching predicate found)
-- Simplified implementation for termination
--/
def typecheckWhile (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p', _  ⟩ := result1.qualType
    if ptyp1 != PTyp.bool then throw "Condition of while must be bool"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
    let branchPc := joinPoison ctx.pc p'
    let ctx'' := { ctx' with pc := branchPc }

    let result2 ← typecheckExpr ctx'' e2 (fuel - 1)
    let ⟨ptyp2, p'', _  ⟩ := result2.qualType
    if ptyp2 != PTyp.unit then throw "Body of while must have unit type"

    -- Simplified: just return unit with combined poison
    let poison := joinPoison ctx.pc (joinPoison p' p'')
    let qt : QTyp := ⟨PTyp.unit, poison, none  ⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv' }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

end

-- Main type checking function
def typecheck (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  typecheckExpr ctx e fuel

/-- Type check an expression in an initial empty context -/
def typecheckExprSimple (e : Expr) : TypecheckM QTyp := do
  let initialCtx : TypeContext := {
    pc := false  -- clean
    memEnv := {}
    varEnv := fun _ => none
    tagEnv := {}
  }
  let result ← typecheck initialCtx e 1000  -- Use 1000 as default fuel
  return result.qualType

/-- Type check a program (expression) and return a human-readable result -/
def typecheckProgram (e : Expr) : String :=
  match typecheckExprSimple e with
  | .ok qualType => s!"Type: {repr qualType}"
  | .error msg => s!"Type error: {msg}"
