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

/-- Join two memory environments (for conditional branches) -/
def joinMemEnvs (env1 env2 : MemoryTypeEnv) : MemoryTypeEnv :=
  -- For now, return union preferring env2 for conflicts
  -- TODO: Implement proper join operation as per Ott spec
  -- TODO: Alternative design: Implement a proper join operation for logical environments where:
  -- - Guards with same value in both branches are preserved
  -- - Guards with contradictory values are removed (become unknown)
  -- - Guards only present in one branch are removed
  -- This would be more precise but adds complexity. The current approach is simpler while

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

-- Helper function to convert Expr to PExpr
def Expr.toPExpr (e : Expr) : TypecheckM PExpr :=
  match e with
  | Expr.value v => return PExpr.value v
  | Expr.var x => return PExpr.var x
  | Expr.op e1 opname e2 => (fun pe1 pe2 => PExpr.op pe1 opname pe2) <$> e1.toPExpr <*> e2.toPExpr
  | Expr.ite e1 e2 e3 => PExpr.ite <$> e1.toPExpr <*> e2.toPExpr <*> e3.toPExpr
  | Expr.deref e => PExpr.deref <$> e.toPExpr
  | Expr.let x e1 e2 => (fun pe1 pe2 => PExpr.let x pe1 pe2) <$> e1.toPExpr <*> e2.toPExpr
  | Expr.app e1 e2 => PExpr.app <$> e1.toPExpr <*> e2.toPExpr
  | _ => throw "Cannot convert expression to PExpr"

-- Helper function to convert PTyp to Typ By stripping poison and closure
-- information from arrows and locations from references.
def PTyp.toTyp (pt : PTyp) : Typ :=
  match pt with
  | PTyp.int => Typ.int
  | PTyp.bool => Typ.bool
  | PTyp.unit => Typ.unit
  | PTyp.ref t _ => Typ.ref (t.toTyp)
  | PTyp.arrow st1 st2 _p _tcl => Typ.arrow st1 st2

-- Helper function to convert PExpr to Expr
def PExpr.toExpr (pe : PExpr) : Expr :=
  match pe with
  | PExpr.value v => Expr.value v
  | PExpr.var x => Expr.var x
  | PExpr.op e1 o e2 => Expr.op (e1.toExpr) o (e2.toExpr)
  | PExpr.ite e1 e2 e3 => Expr.ite (e1.toExpr) (e2.toExpr) (e3.toExpr)
  | PExpr.deref e => Expr.deref (e.toExpr)
  | PExpr.let x e1 e2 => Expr.let x (e1.toExpr) (e2.toExpr)
  | PExpr.app e1 e2 => Expr.app (e1.toExpr) (e2.toExpr)



/-- Convert qualified type to surface type by stripping poison and preducate info -/
def QTyp.toTyp (qt : QTyp) : Typ :=
  qt.ptyp.toTyp

def Address.null : Address := 0
def Name.anonymous : Name := ""

/-- Create a dummy type from a surface type -/
def makeDummyTyp (st : Typ) : PTyp :=
  match st with
  | Typ.int => PTyp.int
  | Typ.bool => PTyp.bool
  | Typ.unit => PTyp.unit
  | Typ.ref t => PTyp.ref (makeDummyTyp t) Address.null
  | Typ.arrow st1 st2 =>
      PTyp.arrow st1 st2 false (TClosure.fn_tclosure Name.anonymous (Expr.value Value.unit) [])

/-- Check if a surface type is a subtype of a qualified type. This implements ST
      <: T by comparing surface types.

    This is as strict comparsion by discarding poison and closure information.
    We can consider implementing proper subtyping relation with contravariance
    for the parameter type and covariance for the return type in the future.
-/
def isSubtype (st : Typ) (qt : QTyp) : Bool :=
  qt.toTyp == st

/--
  For any n ≠ 0, `n.pred < n`.
  (Lean's `termination_by` always gives you `h : n ≠ 0` in the context,
   so this lines up perfectly.)
-/
theorem Nat.pred_lt_of_ne_zero {n : Nat} (h : n ≠ 0) : n - 1 < n := by
  cases n
  · contradiction
  · apply Nat.lt_succ_self

-- Helper function to check if two PExprs are syntactically equal modulo
-- environment differences. This handles variable substitution and type
-- compatibility checking during structural comparison. Variables are
-- substituted in the first argument only.
--
-- The `fuel` parameter is used to help the termination checker.
-- The `substitution` parameter is an optional (variable, value) pair for substitution.
--
def PExpr.equalWithEnvs (pe1 : PExpr) (env1 : VarTypeEnv) (pe2 : PExpr) (env2 : VarTypeEnv) (substitution : Option (Name × PExpr)) (fuel : Nat) : Bool :=
  if fuel = 0 then false
  else
    match pe1, pe2 with
    | PExpr.value v1, PExpr.value v2 => v1 == v2
    | PExpr.var x1, pe2 =>
        match substitution with
        | some (arg1, val1) =>
          if x1 == arg1 then
            -- This is the variable we're substituting, substitute it with the value
            PExpr.equalWithEnvs val1 env1 pe2 env2 substitution (fuel - 1)
          else
            -- Some other variable, compare it syntactically with the target variable
            match pe2 with
            | PExpr.var x2 => x1 == x2
            | _ => false
        | none =>
          -- No substitution active, just compare variables syntactically
          match pe2 with
          | PExpr.var x2 => x1 == x2
          | _ => false
    | PExpr.op e1 op1 e2, PExpr.op e1' op2 e2' =>
      op1 == op2 && equalWithEnvs e1 env1 e1' env2 substitution (fuel - 1) && equalWithEnvs e2 env1 e2' env2 substitution (fuel - 1)
    | PExpr.ite e1 e2 e3, PExpr.ite e1' e2' e3' =>
      equalWithEnvs e1 env1 e1' env2 substitution (fuel - 1) && equalWithEnvs e2 env1 e2' env2 substitution (fuel - 1) && equalWithEnvs e3 env1 e3' env2 substitution (fuel - 1)
    | PExpr.deref e1, PExpr.deref e2 => equalWithEnvs e1 env1 e2 env2 substitution (fuel - 1)
    | PExpr.let x1 e1 e2, PExpr.let x2 e1' e2' =>
      x1 == x2 &&
      equalWithEnvs e1 env1 e1' env2 substitution (fuel - 1) &&
      -- For the body, disable substitution if the bound variable shadows the substitution variable
      equalWithEnvs e2 env1 e2' env2 (if substitution.map (·.1) == some x1 then none else substitution) (fuel - 1)
    | PExpr.app e1 e2, PExpr.app e1' e2' =>
      equalWithEnvs e1 env1 e1' env2 substitution (fuel - 1) && equalWithEnvs e2 env1 e2' env2 substitution (fuel - 1)
    | _, _ => false
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/--
  Scans the predicates attached to every variable in S and every memory location
  in G which has a variable in S referencing it; if it finds exactly one guard k
  whose test expression, when applied to its owning value (variable or deref of
  variable), is syntactically identical to the condition e, it returns that k -
  otherwise it throws an error.

  We perform variable substitution in the predicate body before comparing it to
  the condition using PExpr.equalWithEnvs for proper environment-aware
  comparison.
--/
def matchGuard (e : Expr) (G : MemoryTypeEnv) (S : VarTypeEnv) : TypecheckM Tag := do
  -- Try to convert the condition e to a PExpr
  let conditionPExpr ← e.toPExpr

  -- Helper function to check if a predicate's test expression matches the condition
  let checkPredicate (arg : PExpr) (qt : QTyp) : TypecheckM (Option Tag) :=
    match qt.pred with
    | none => return none
    | some ⟨tag, arg_name, pred_body, var_env⟩ =>
              -- Compare the predicate body with the condition using environment-aware equality
        if PExpr.equalWithEnvs pred_body var_env conditionPExpr S (some (arg_name, arg)) 100 then return some tag else return none

  -- Collect all matching tags from variable environment
    let varMatches := S.foldl (init := []) fun acc ⟨name, qt⟩ =>
    let arg := PExpr.var name
    match checkPredicate arg qt with
    | .ok (some tag) => tag :: acc
    | .ok none => acc
    | .error _ => acc

  -- For references, we need to check the memory environment
  let refMatches := S.foldl (init := []) fun acc ⟨name, qt⟩ =>
    -- Check if the variable has a reference type
    match qt.ptyp with
    | PTyp.ref _t l =>
      -- Look up the memory location in G
      match G.get? l with
      | some memQt =>
        -- Use the dereferenced value as the substitution value
        let arg := PExpr.deref (PExpr.var name)
        -- Use checkPredicate to check if the memory location's predicate matches
        match checkPredicate arg memQt with
        | .ok (some tag) => tag :: acc
        | .ok none => acc
        | .error _ => acc
      | none => acc
    | _ => acc

  let allMatches := varMatches ++ refMatches
  -- Return the tag if exactly one match is found, otherwise throw an error
  match allMatches with
  | [tag] => return tag
  | [] => throw "No matching guard found for condition"
  | _ => throw s!"Multiple matching guards found for condition: {allMatches}"



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
  match lookupVarEnv ctx.varEnv x with
  | some qt =>
    let ⟨ptyp, poison, pred⟩ := qt
    match pred with
    | none =>  -- no_pred case
      let poison := joinPoison ctx.pc poison
      let qt' : QTyp := ⟨ptyp, poison, none ⟩
      return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
    | some tp =>  -- has predicate
      let ⟨k, arg_name, pred_body, var_env⟩ := tp
      match ctx.tagEnv.get? k with
      | some true =>  -- guard_true case
        let qt' : QTyp := ⟨ptyp, ctx.pc, none ⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
      | some false =>  -- guard_false case
        let qt' : QTyp := ⟨ptyp, true, none ⟩  -- poisoned
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
      | none =>  -- guard_unknown case
        let poison := joinPoison ctx.pc poison
        let tp' : TPred := ⟨k, arg_name, pred_body, var_env⟩
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



-- The following option is needed in increasing the maximum number of heartbeats
-- to avoid the termination checker failure on the following mutual block.
set_option maxHeartbeats 800000


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
    | Expr.fn x t body => typecheckFn ctx x t body (fuel - 1)
    | Expr.pfn x t body => typecheckPfn ctx x t body (fuel - 1)
    | Expr.app e1 e2 => typecheckApp ctx e1 e2 (fuel - 1)
    | Expr.ite e1 e2 e3 => typecheckIf ctx e1 e2 e3 (fuel - 1)
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Helper function to derive return type ST2 from function body
   This implements the common logic for both fn_abs and pfn_abs rules:
   - Create dummy type T1 from surface type ST1
   - Typecheck body with dummy argument type T1
   - Convert body type T2 to surface type ST2
-/
def deriveReturnType (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (fuel : Nat) : TypecheckM Typ :=
  if fuel = 0 then throw "Out of fuel"
  else do
    -- Create dummy type T1 from surface type ST1 to typecheck the body
    let t1 := makeDummyTyp st1

    -- Update context with dummy argument type T1
    let varEnv' := updateVarEnv ctx.varEnv x (⟨t1, ctx.pc, none⟩)
    let ctx' := { ctx with varEnv := varEnv' }

    -- Typecheck body with dummy argument type T1
    let result ← typecheckExpr ctx' body (fuel - 1)
    let ⟨t2, _p, _pred⟩ := result.qualType

  -- Convert body type T2 to surface type ST2
    return t2.toTyp
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
    let storedPoison := joinPoison ctx.pc poison
    let storedQt : QTyp := ⟨ptyp, storedPoison, pred  ⟩
    let memEnv' := updateMemEnv result.memEnv' l storedQt

    let qt : QTyp := ⟨PTyp.ref ptyp l, ctx.pc, none  ⟩
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
  pc ; G ; S ; L |- e : ref T @ l :> p' { P' } -| G' ; L'
  G'(l) = T :> p { no_pred }
  ----------------------- :: deref_no_pred
  pc ; G ; S ; L |- !e : T :> join pc join p' p { no_pred } -| G' ; L'
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
        if ptyp' != t then throw s!"Type mismatch in dereference: {repr ptyp'} != {repr t}"
        let poison := joinPoison ctx.pc (joinPoison poison p2)
        let qt : QTyp := ⟨t, poison, none  ⟩
        return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv' }
      | some ⟨ptyp', p2, some ⟨k, arg_name, pred_body, var_env⟩ ⟩ =>  -- has predicate
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
          let qt : QTyp := ⟨t, poison, some ⟨k, arg_name, pred_body, var_env⟩ ⟩
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
  pc ; G ; S[x |-> T1 :> pc { no_pred }] ; L |- e : T2 :> p' { P' } -| G' ; L'
  ST1 <: T1
  ST2 <: T2
----------------------------------------------------------------------  :: fn_abs
  pc ; G ; S ; L |- fn x : ST1 => e : ST1 -> ST2 # pc typing_closure ( x , e , S ) :> pc { no_pred } -| G ; L
-/
def typecheckFn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    -- Derive return type ST2 from function body
    let st2 ← deriveReturnType ctx x st1 body (fuel - 1)

    -- Create arrow type ST1 -> ST2
    let arrowTyp : PTyp := PTyp.arrow st1 st2 false (TClosure.fn_tclosure x body ctx.varEnv)

    -- Create qualified type ST1 -> ST2 # pc { no_pred }
    let qt : QTyp := ⟨arrowTyp, ctx.pc, none⟩

    return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›

/-- Rule: pfn_abs (Ott rule: pfn_abs)
  pc ; G ; S[x |-> T1 :> pc { no_pred }] ; L |- pe : T2 :> p' { P' } -| G' ; L'
  ST1 <: T1
  ST2 <: T2
----------------------------------------------------------------------  :: pfn_abs
  pc ; G ; S ; L |- pfn x : ST1 => pe : ST1 -> ST2 # pc typing_closure ( x , pe , S ) :> pc { no_pred } -| G ; L
-/
def typecheckPfn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    -- Derive return type ST2 from function body
    let st2 ← deriveReturnType ctx x st1 body (fuel - 1)

    -- Convert body to PExpr
    let pbody ← body.toPExpr

    -- Create arrow type ST1 -> ST2
    let arrowTyp : PTyp := PTyp.arrow st1 st2 false (TClosure.pfn_tclosure x pbody ctx.varEnv)

    -- Create qualified type ST1 -> ST2 # pc { no_pred }
    let qt : QTyp := ⟨arrowTyp, ctx.pc, none⟩

    return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }
termination_by fuel
decreasing_by
  all_goals exact Nat.pred_lt_of_ne_zero ‹fuel ≠ 0›


/-- Rule: app_fn (Ott rules: app_fn, app_pfn)
  pc ; G ; S ; L |- e1 : ST1 -> ST2 # p typing_closure ( x , e , S' ) :> p1 { P1 } -| G' ; L'
  pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
  ST1 <: T1
  pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- e : T2 :> p3 { P3 } -| G''' ; L'''
  ST2 <: T2
----------------------------------------------------------------------  :: app_fn
  pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''


  pc ; G ; S ; L |- e1 : ST1 -> ST2 # p typing_closure ( x , pe , S' ) :> p1 { P1 } -| G' ; L'
  pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
  ST1 <: T1
  pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- pe : T2 :> p3 { P3 } -| G''' ; L'''
  ST2 <: T2
----------------------------------------------------------------------  :: app_pfn
  pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''

-/
def typecheckApp (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    -- Premise 1: pc ; G ; S ; L |- e1 : ST1 -> ST2 # p typing_closure ( x , e , S' ) :> p1 { P1 } -| G' ; L'
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, _p1, _pred1⟩ := result1.qualType
    match ptyp1 with
    | PTyp.arrow st1 st2 _p tcl =>
      -- Premise 2: pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
      let result2 ← typecheckExpr ctx' e2 (fuel - 1)
      let ⟨ptyp2, p2, pred2⟩ := result2.qualType

      -- Premise 3: ST1 <: T1 (check subtyping)
      if not (isSubtype st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr result2.qualType.toTyp}"

      match tcl with
      | TClosure.fn_tclosure x body env =>
        -- Premise 4: pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- e : T2 :> p3 { P3 } -| G''' ; L'''
        let argQt : QTyp := ⟨ptyp2, joinPoison ctx.pc p2, pred2⟩
        let env' := updateVarEnv env x argQt
        let ctx'' := { ctx with memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv' }
        let result3 ← typecheckExpr ctx'' body (fuel - 1)
        let ⟨ptyp3, p3, pred3⟩ := result3.qualType

        -- Premise 5: ST2 <: T2 (check subtyping)
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr result3.qualType.toTyp}"

        -- Conclusion: pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨ptyp3, poison, pred3⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv' }

      | TClosure.pfn_tclosure x body env =>
        -- Premise 4: pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- pe : T2 :> p3 { P3 } -| G''' ; L'''
        let argQt : QTyp := ⟨ptyp2, joinPoison ctx.pc p2, pred2⟩
        let env' := updateVarEnv env x argQt
        let ctx'' := { ctx with memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv' }
        let result3 ← typecheckExpr ctx'' (body.toExpr) (fuel - 1)
        let ⟨ptyp3, p3, pred3⟩ := result3.qualType

        -- Premise 5: ST2 <: T2 (check subtyping)
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr result3.qualType.toTyp}"

        -- Conclusion: pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨ptyp3, poison, pred3⟩
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

/-- Rule: if_depoison and if_std (Ott rules: if_depoison when matchGuard succeeds, if_std when it fails)
-- First tries predicate-based de-poisoning, falls back to standard conditional typing
--/
def typecheckIf (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p', _  ⟩ := result1.qualType
    if ptyp1 != PTyp.bool then throw "Condition of if must be bool"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }

    -- Try predicate-based de-poisoning first
    match matchGuard e1 result1.memEnv' ctx.varEnv with
    | .ok k => do
      -- Predicate-based case (if_depoison)
      let branchPc := joinPoison ctx.pc p'
      let ctx'' := { ctx' with pc := branchPc }

      -- Type check both branches with updated tag environment
      let ctxTrue := { ctx'' with tagEnv := ctx''.tagEnv.insert k true }
      let ctxFalse := { ctx'' with tagEnv := ctx''.tagEnv.insert k false }

      let result2 ← typecheckExpr ctxTrue e2 (fuel - 1)
      let ⟨ptyp2, p'', _  ⟩ := result2.qualType

      let result3 ← typecheckExpr ctxFalse e3 (fuel - 1)
      let ⟨ptyp3, p''', _  ⟩ := result3.qualType

      if ptyp2 != ptyp3 then throw "Branches of if must have same type"

      let poison := joinPoison ctx.pc (joinPoison p' (joinPoison p'' p'''))
      let qt : QTyp := ⟨ptyp2, poison, none  ⟩
      let memEnv' := joinMemEnvs result2.memEnv' result3.memEnv'
      -- Return original tag environment (k becomes unknown after conditional)
      return { qualType := qt, memEnv' := memEnv', tagEnv' := ctx'.tagEnv }

    | .error _ => do
      -- Standard case (if_std) - no matching predicate found
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

/-- Rule: while_depoison and while_std (Ott rules: while_depoison when matchGuard succeeds, while_std when it fails)
-- First tries predicate-based de-poisoning, falls back to standard while typing
-- Simplified implementation for termination
--/
def typecheckWhile (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  if fuel = 0 then throw "Out of fuel"
  else do
    let result1 ← typecheckExpr ctx e1 (fuel - 1)
    let ⟨ptyp1, p', _  ⟩ := result1.qualType
    if ptyp1 != PTyp.bool then throw "Condition of while must be bool"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }

    -- Try predicate-based de-poisoning first
    match matchGuard e1 result1.memEnv' ctx.varEnv with
    | .ok k => do
      -- Predicate-based case (while_depoison) - simplified implementation
      let branchPc := joinPoison ctx.pc p'
      let ctx'' := { ctx' with pc := branchPc }

      let result2 ← typecheckExpr ctx'' e2 (fuel - 1)
      let ⟨ptyp2, p'', _  ⟩ := result2.qualType
      if ptyp2 != PTyp.unit then throw "Body of while must have unit type"

      -- Simplified: just return unit with combined poison
      let poison := joinPoison ctx.pc (joinPoison p' p'')
      let qt : QTyp := ⟨PTyp.unit, poison, none  ⟩
      -- Set k to false after loop (as per Ott spec)
      let tagEnv' := ctx'.tagEnv.insert k false
      return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := tagEnv' }

    | .error _ => do
      -- Standard case (while_std) - no matching predicate found
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
    varEnv := []
    tagEnv := {}
  }
  let result ← typecheck initialCtx e 1000  -- Use 1000 as default fuel
  return result.qualType

/-- Type check a program (expression) and return a human-readable result -/
def typecheckProgram (e : Expr) : String :=
  match typecheckExprSimple e with
  | .ok qualType => s!"Type: {repr qualType}"
  | .error msg => s!"Type error: {msg}"
