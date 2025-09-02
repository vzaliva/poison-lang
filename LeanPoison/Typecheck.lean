import LeanPoison.Syntax
import LeanPoison.Poison
import Std.Data.HashMap
open Std

-- Type checking environment definitions

/-- Default fuel for type checking -/
private def defaultFuel : Nat := 1000

/-- Memory typing environment (Γ in the Ott spec) -/
abbrev MemoryTypeEnv := HashMap Address QTyp

namespace MemoryTypeEnv

  @[inline] def lookup (m : MemoryTypeEnv) (a : Address) : Option QTyp :=
    m.get? a

  @[inline] def update (m : MemoryTypeEnv) (a : Address) (qt : QTyp) : MemoryTypeEnv :=
    m.insert a qt

  /-- `m` contains a binding for `a`. -/
  def hasKey (m : MemoryTypeEnv) (a : Address) : Prop :=
    m.contains a

end MemoryTypeEnv


/-- Tag valuation environment (ℒ in the Ott spec) -/
abbrev TagEnv := HashMap Tag Bool

/-- Type checking context containing all environments -/
structure TypeContext where
  pc : Poison            -- Poison context
  memEnv : MemoryTypeEnv -- Γ
  varEnv : VarTypeEnv    -- σ
  tagEnv : TagEnv        -- ℒ
  nextLoc : Address  -- for fresh location generation
  nextTag : Tag  -- for fresh location generation

/-- Type checking result: qualified type and updated memory environment -/
structure TypeResult where
  qualType : QTyp -- Qualified type of the expression
  memEnv' : MemoryTypeEnv -- Updated memory typing environment
  tagEnv' : TagEnv  -- Updated logical environment
  nextLoc' : Address -- Updated next location
  nextTag' : Tag -- Updated next location

/-- Type checking monad for error handling -/
abbrev TypecheckM := Except String

-- Allocate a fresh location and return it along with updated typing context
def freshTLoc (ctx : TypeContext): (Address × TypeContext) :=
  (ctx.nextLoc, { ctx with nextLoc := ctx.nextLoc + 1 })

-- Allocate a fresh location and return it along with updated typing context
def freshTLocRes (result : TypeResult): (Address × TypeResult) :=
  (result.nextLoc', { result with nextLoc' := result.nextLoc' + 1 })

-- Function to get a fresh Tag Value From the environment
def generateFreshTag (ctx : TypeContext) : (Tag × TypeContext) :=
  (ctx.nextTag, { ctx with nextTag := ctx.nextTag + 1 })

-- Allocate a fresh Tag Value and return it along with updated typing result
def generateFreshTagRes (result : TypeResult): (Tag × TypeResult) :=
  (result.nextTag', { result with nextTag' := result.nextTag' + 1 })


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

-- Helper function to convert Expr to PExpr
def Expr.toPExpr (e : Expr) : TypecheckM PExpr :=
  match e with
  | Expr.num n => return PExpr.value (Value.num n)
  | Expr.bool b => return PExpr.value (Value.bool b)
  | Expr.unit => return PExpr.value Value.unit
  | Expr.var x => return PExpr.var x
  | Expr.op e1 opname e2 => (fun pe1 pe2 => PExpr.op pe1 opname pe2) <$> e1.toPExpr <*> e2.toPExpr
  | Expr.ite e1 e2 e3 => PExpr.ite <$> e1.toPExpr <*> e2.toPExpr <*> e3.toPExpr
  | Expr.deref e => PExpr.deref <$> e.toPExpr
  | Expr.vlet x e1 e2 => (fun pe1 pe2 => PExpr.vlet x pe1 pe2) <$> e1.toPExpr <*> e2.toPExpr
  | Expr.app e1 e2 => PExpr.app <$> e1.toPExpr <*> e2.toPExpr
  | _ => throw "Cannot convert expression to PExpr"

-- Helper function to project ETyp to Typ By stripping poison and closure
-- information from arrows and locations from references.
def ETyp.toTyp (pt : ETyp) : Typ :=
  match pt with
  | ETyp.int => Typ.int
  | ETyp.bool => Typ.bool
  | ETyp.unit => Typ.unit
  | ETyp.string => Typ.string
  | ETyp.ref t _ => Typ.ref (t.toTyp)
  | ETyp.arrow st1 st2 _p _tcl => Typ.arrow st1 st2
  | ETyp.parrow st1 st2 _p _tcl => Typ.arrow st1 st2

-- Helper function to convert PExpr to Expr
def PExpr.toExpr (pe : PExpr) : Expr :=
  match pe with
  | PExpr.value (Value.num n) => Expr.num n
  | PExpr.value (Value.bool b) => Expr.bool b
  | PExpr.value Value.unit => Expr.unit
  | PExpr.value _ => Expr.unit  -- For other values that can't be represented as expressions
  | PExpr.var x => Expr.var x
  | PExpr.op e1 o e2 => Expr.op (e1.toExpr) o (e2.toExpr)
  | PExpr.ite e1 e2 e3 => Expr.ite (e1.toExpr) (e2.toExpr) (e3.toExpr)
  | PExpr.deref e => Expr.deref (e.toExpr)
  | PExpr.vlet x e1 e2 => Expr.vlet x (e1.toExpr) (e2.toExpr)
  | PExpr.app e1 e2 => Expr.app (e1.toExpr) (e2.toExpr)



/-- Convert qualified type to surface type by stripping poison and preducate info -/
def QTyp.toTyp (qt : QTyp) : Typ :=
  qt.etyp.toTyp





/-- Check if a surface type is a subtype of a qualified type. This implements ST
      <: T by comparing surface types.

    This is as strict comparsion by discarding poison and closure information.
    We can consider implementing proper subtyping relation with contravariance
    for the parameter type and covariance for the return type in the future.
-/
def isSubtype (st : Typ) (qt : QTyp) : Bool :=
  qt.toTyp == st


-- Typing judgement for operations
inductive OpEType : Op → ETyp → ETyp → ETyp → Prop where
  | add_int : OpEType Op.add ETyp.int ETyp.int ETyp.int
  | sub_int : OpEType Op.sub ETyp.int ETyp.int ETyp.int
  | mul_int : OpEType Op.mul ETyp.int ETyp.int ETyp.int
  | div_int : OpEType Op.div ETyp.int ETyp.int ETyp.int

  | gte_int : OpEType Op.gte ETyp.int ETyp.int ETyp.bool
  | lte_int : OpEType Op.lte ETyp.int ETyp.int ETyp.bool
  | gt_int  : OpEType Op.gt  ETyp.int ETyp.int ETyp.bool
  | lt_int  : OpEType Op.lt  ETyp.int ETyp.int ETyp.bool
  | eq_int  : OpEType Op.eq  ETyp.int ETyp.int ETyp.bool

  | and_bool : OpEType Op.and ETyp.bool ETyp.bool ETyp.bool
  | or_bool  : OpEType Op.or  ETyp.bool ETyp.bool ETyp.bool

def opEType? : Op → ETyp → ETyp → Option ETyp
  | .add, .int,  .int  => some .int
  | .sub, .int,  .int  => some .int
  | .mul, .int,  .int  => some .int
  | .div, .int,  .int  => some .int
  | .gte, .int,  .int  => some .bool
  | .lte, .int,  .int  => some .bool
  | .gt,  .int,  .int  => some .bool
  | .lt,  .int,  .int  => some .bool
  | .eq,  .int,  .int  => some .bool
  | .and, .bool, .bool => some .bool
  | .or,  .bool, .bool => some .bool
  | _,    _,     _     => none



/--
 Helper function to check if two PExprs are syntactically equal modulo
 environment differences. This handles variable substitution and type
 compatibility checking during structural comparison. Variables are substituted
 in the first argument only.

 The `fuel` parameter is used to prove termination. Normally we should be able
 should be able to prove termination on structure of pe1 and pe2 arguments but
 this is does not work in case of substitution. In fact, unless isValidSubstitution
 is ensured in matchGuard, we will get infinite recursion.

 The `substitution` parameter is an optional (variable, value) pair for
 substitution.
--/
def PExpr.equalWithEnvs (pe1 : PExpr) (env1 : VarTypeEnv) (pe2 : PExpr) (env2 : VarTypeEnv) (substitution : Option (Name × PExpr)) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 =>
    match pe1, pe2 with
    | PExpr.value v1, PExpr.value v2 => v1 == v2
    | PExpr.var x1, pe2 =>
        match substitution with
        | some (arg1, val1) =>
          if x1 == arg1 then
            -- If we're substituting x with x, just compare syntactically
            if val1 == PExpr.var x1 then
              match pe2 with
              | PExpr.var x2 => x1 == x2
              | _ => false
            else
              -- Normal substitution
              PExpr.equalWithEnvs val1 env1 pe2 env2 substitution fuel
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
      op1 == op2 && equalWithEnvs e1 env1 e1' env2 substitution fuel && equalWithEnvs e2 env1 e2' env2 substitution fuel
    | PExpr.ite e1 e2 e3, PExpr.ite e1' e2' e3' =>
      equalWithEnvs e1 env1 e1' env2 substitution fuel && equalWithEnvs e2 env1 e2' env2 substitution fuel && equalWithEnvs e3 env1 e3' env2 substitution fuel
    | PExpr.deref e1, PExpr.deref e2 => equalWithEnvs e1 env1 e2 env2 substitution fuel
    | PExpr.vlet x1 e1 e2, PExpr.vlet x2 e1' e2' =>
      x1 == x2 &&
      equalWithEnvs e1 env1 e1' env2 substitution fuel &&
      -- For the body, disable substitution if the bound variable shadows the substitution variable
      equalWithEnvs e2 env1 e2' env2 (if substitution.map (·.1) == some x1 then none else substitution) fuel
    | PExpr.app e1 e2, PExpr.app e1' e2' =>
      equalWithEnvs e1 env1 e1' env2 substitution fuel && equalWithEnvs e2 env1 e2' env2 substitution fuel
    | _, _ => false


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
        if PExpr.equalWithEnvs pred_body var_env conditionPExpr S (some (arg_name, arg)) defaultFuel then return some tag else return none

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
      match qt.etyp with
  | ETyp.ref _t l =>
      if qt.poison then
        -- Poisoned reference: it could never be de-poisoned, so we don't need to check the predicate
        acc
      else
        -- Look up the type of the memory location in G
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
def typecheckInt (ctx : TypeContext) (_n : Int) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.int, false, none⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

/-- Rule: bool (Ott rule: bool)
-- pc ; G ; S ; L |- b : bool :> clean { no_pred } -| G ; L
-/
def typecheckBool (ctx : TypeContext) (_b : Bool) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.bool, false, none ⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }


/-- Rules: var_guard_true, var_guard_false, var_guard_unknown, var_no_pred (Ott rules)
-- Variable typing with predicate handling:
-- - var_guard_true: S(x) = T :> p { guard k pred_closure pcl }, L(k) = true
-- - var_guard_false: S(x) = T :> p { guard k pred_closure pcl }, L(k) = false
-- - var_guard_unknown: S(x) = T :> p { guard k pred_closure pcl }, k not in L
-- - var_no_pred: S(x) = T :> p { no_pred }
--/
def typecheckVar (ctx : TypeContext) (x : Name) : TypecheckM TypeResult := do
  --dbg_trace "Typechecking var "
  --dbg_trace x
  --dbg_trace "ctx.pc is"
  --dbg_trace ctx.pc
  match ctx.varEnv.lookup x with
  | some qt =>
    let ⟨etyp, poison, pred⟩ := qt
    match pred with
    | none =>  -- no_pred case
      let poison := joinPoison ctx.pc poison
      let qt' : QTyp := ⟨etyp, poison, none ⟩
      return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
    | some tp =>  -- has predicate
      let ⟨k, arg_name, pred_body, var_env⟩ := tp
     -- dbg_trace "In typeCheckVar"
     -- dbg_trace k
      match ctx.tagEnv.get? k with
      | some true =>  -- guard_true case
       -- dbg_trace "Guard True case"
        let qt' : QTyp := ⟨etyp, ctx.pc, none ⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
      | some false =>  -- guard_false case
       -- dbg_trace "Guard False case"
        let qt' : QTyp := ⟨etyp, true, none ⟩  -- poisoned
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
      | none =>  -- guard_unknown case
       -- dbg_trace "Guard Unknown case"
        let poison := joinPoison ctx.pc poison
        let tp' : TPred := ⟨k, arg_name, pred_body, var_env⟩
        let qt' : QTyp := ⟨etyp, poison, some tp' ⟩
        return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
  | none => throw s!"Variable {x} not found in environment"


/-- Rule: location (Ott rule: location)
-- G(l) = T :> p { P }
-- ------------------
-- pc ; G ; S ; L |- l : ref T @ l :> clean { no_pred } -| G ; L
-/
def typecheckLocation (ctx : TypeContext) (l : Address) : TypecheckM TypeResult := do
  match ctx.memEnv.get? l with
  | some qt =>
    let ⟨etyp, _p, pred ⟩ := qt
    let refTyp := ETyp.ref etyp l
    let qt' : QTyp := ⟨refTyp, false, pred ⟩  -- clean, no predicate
    return { qualType := qt', memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
  | none => throw s!"Location {l} not found in memory environment"

/-- Rule: unit (Ott rule: unit)
-- pc ; G ; S ; L |- unit : unit :> clean { no_pred } -| G ; L
-/
def typecheckUnit (ctx : TypeContext) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.unit, false, none  ⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

/--  Rule: string (Ott rule: string)
-- pc ; G ; S ; L |- string : string :> clean { no_pred } -| G ; L
-/
def typecheckString (ctx : TypeContext) (_s : String) : TypecheckM TypeResult := do
  let qt : QTyp := ⟨ETyp.string, false, none  ⟩  -- clean, no predicate
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

-- The following option is needed in increasing the maximum number of heartbeats
-- to avoid the termination checker failure on the following mutual block.
set_option maxHeartbeats 800000


/-- Rule: fn_abs (Ott rule: fn_abs)
----------------------------------------------------------------------  :: fn_abs
  pc ; G ; S ; L |- fn x : ST1 => e : ST1 -> ST2 # pc typing_closure ( x , e , S ) :> pc { no_pred } -| G ; L
-/
def typecheckFn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (st2 : Typ) : TypecheckM TypeResult :=
  -- Simply record the body and return type without typechecking the body
  -- Body typechecking is deferred until application time

  -- Create arrow type ST1 -> ST2
  let arrowTyp : ETyp := ETyp.arrow st1 st2 false (FnTClosure.mk x body ctx.varEnv)
  -- Create qualified type ST1 -> ST2 # pc { no_pred }
  let qt : QTyp := ⟨arrowTyp, ctx.pc, none⟩
   return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

/-- Rule: pfn_abs (Ott rule: pfn_abs)
----------------------------------------------------------------------  :: pfn_abs
  pc ; G ; S ; L |- pfn x : ST1 => pe : ST1 -> ST2 # pc typing_closure ( x , pe , S ) :> pc { no_pred } -| G ; L
-/
def typecheckPfn (ctx : TypeContext) (x : Name) (st1 : Typ) (body : Expr) (st2 : Typ) : TypecheckM TypeResult := do
  -- Simply record the body and return type without typechecking the body
  -- Body typechecking is deferred until application time

   -- Convert body to PExpr
  let pbody ← body.toPExpr
  -- Create arrow type ST1 -> ST2
  let arrowTyp : ETyp := ETyp.parrow st1 st2 false (PFnTClosure.mk x pbody ctx.varEnv)
  -- Create qualified type ST1 -> ST2 # pc { no_pred }
  let qt : QTyp := ⟨arrowTyp, ctx.pc, none⟩

  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }



def generateFreshVar (ctx : TypeContext) (pref : Name) (suffix : Nat) (fuel : Nat) : Name :=
  match fuel with
  | 0 => s!"{pref}{suffix}"
  | fuel + 1 =>
      let candidate := if suffix = 0 then pref else s!"{pref}{suffix}"
      if candidate ∈ ctx.varEnv.map (·.fst) then
       generateFreshVar ctx pref (suffix + 1) fuel
      else
       candidate
termination_by fuel


mutual

-- Helper function to type check an expression with context
def typecheckExpr (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    match e with
    | Expr.num n => typecheckInt ctx n
    | Expr.bool b => typecheckBool ctx b
    | Expr.unit => typecheckUnit ctx
    | Expr.str s => typecheckString ctx s
    | Expr.var x => typecheckVar ctx x
    | Expr.op e1 op e2 => typecheckOp ctx e1 e2 fuel op
    | Expr.newRef e => typecheckNewRef ctx e fuel
    | Expr.assign e1 e2 => typecheckAssign ctx e1 e2 fuel
    | Expr.deref e1 => typecheckDeref ctx e1 fuel
    | Expr.seq e1 e2 => typecheckSeq ctx e1 e2 fuel
    | Expr.kwhile e1 e2 => typecheckWhile ctx e1 e2 fuel
    | Expr.vlet x e1 e2 => typecheckVlet ctx x e1 e2 fuel
    | Expr.fn x paramType body returnType => typecheckFn ctx x paramType body returnType
    | Expr.pfn x paramType body returnType => typecheckPfn ctx x paramType body returnType
    | Expr.app e1 e2 => typecheckApp ctx e1 e2 fuel
    | Expr.ite e1 e2 e3 => typecheckIf ctx e1 e2 e3 fuel
    | Expr.rand e => typecheckRand ctx  e fuel
    | Expr.frand e => typecheckFrand ctx e fuel
    | Expr.printString e => typecheckPrintString ctx e fuel
    | Expr.printInt e => typecheckPrintInt ctx e fuel
termination_by fuel



/- Rule : Ty rand typing
                pc; Γ; σ; L ⊢ e : int ▷ p {P} ⊣ Γ′; L′
                ---------------------------------------------------
                pc; Γ; σ; L ⊢ rand e : int ▷ pc ⊔ p {} ⊣ Γ′; L′
-/
def typecheckRand (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do
              let result ← typecheckExpr ctx e (fuel - 1)
              let ⟨etyp, poison, _  ⟩ := result.qualType
              if etyp != ETyp.int then throw ("Argument Expression to rand must have type int")
              else
                let qt' : QTyp := ⟨ETyp.int , joinPoison ctx.pc poison, none ⟩
                return {result with qualType := qt' }
termination_by fuel

/- Rule: Ty frand typing
                  pc; Γ; σ; L ⊢ pe : int ▷ p {P} ⊣ Γ; L
                  fresh k
                  fresh x σ
                  pcl = (0 ≤ x ≤ pe, σ)
                  ------------------------------------------------------------------
                  pc; Γ; σ; L ⊢ frand pe : int ▷ poisoned {guard k pred closure pcl} ⊣ Γ; L

-/
def typecheckFrand (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
  | 0        => throw "Out of fuel"
  | fuel + 1 =>
    do
      let result ← typecheckExpr ctx e (fuel - 1)
      let ⟨etyp, _, _  ⟩ := result.qualType
      if etyp != ETyp.int then throw ("Argument Expression to frand must have type int")
      else
        let (newTag,result') := generateFreshTagRes result
        let varName := generateFreshVar ctx "limit" 0 fuel
        let predBody : PExpr <- Expr.toPExpr (Expr.op (Expr.op (Expr.var varName) Op.gte (Expr.num 0)) Op.and
                                 (Expr.op (Expr.var varName) Op.lte ( e)) )

        let depoisoningPred : TPred := ⟨ newTag  , varName  , predBody , ctx.varEnv⟩

        let qt' : QTyp := ⟨ETyp.int , true, some depoisoningPred ⟩
        return {result' with qualType := qt'}
termination_by fuel

/-
      pc ; G ; S ; L |- e : string :> p { P } -| G' ; L'
    ----------------------------------------------------------------------  :: printString_typing
      pc ; G ; S ; L |- printString e : unit :> join pc p { no_pred } -| G' ; L'
 -/
def typecheckPrintString (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do

              let result ← typecheckExpr ctx e fuel
              let ⟨etyp, poison, _  ⟩ := result.qualType
              if etyp != ETyp.string then throw ("Argument Expression to printString must have type string")
              else
                let qt' : QTyp := ⟨ETyp.unit , joinPoison ctx.pc poison, none ⟩
                return {result with qualType := qt' }
termination_by fuel

/-
              pc ; G ; S ; L |- e : int :> p { P } -| G' ; L'
    ----------------------------------------------------------------------  :: printInt_typing
      pc ; G ; S ; L |- printInt e : unit :> join pc p { no_pred } -| G' ; L'

 -/
def typecheckPrintInt (ctx : TypeContext) (e : Expr) (fuel : Nat):TypecheckM TypeResult :=
  match fuel with
    | 0        => throw "Out of fuel"
    | fuel + 1 =>
            do
              let result ← typecheckExpr ctx e fuel
              let ⟨etyp, poison, _  ⟩ := result.qualType
              if etyp != ETyp.int then throw ("Argument Expression to printInt must have type int")
              else
                let qt' : QTyp := ⟨ETyp.unit , joinPoison ctx.pc poison, none ⟩
                return {result with qualType := qt' }
termination_by fuel

/- Function to typecheck expressions in a binary-operation Expression, ensuring
   both expressions in a binary-op expression must be Integers .
-/
/-- Rule: op
-- pc ; G ; S ; L |- e1 : int :> p' { P1 } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : int :> p'' { P2 } -| G'' ; L''
-- op ∈ {+,-,*,/,>,>=,<,<=,==}
-- --------------------------------
-- pc ; G ; S ; L |- e1 op e2 : int :> join pc join p' p'' { no_pred } -| G'' ; L''
-/
def typecheckOp (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) (op : Op) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
    let result2 ← typecheckExpr ctx' e2 fuel
    let ⟨etyp2, p2, _  ⟩ := result2.qualType

    match opEType? op etyp1 etyp2 with
    | some r =>
        let poison := joinPoison ctx.pc (joinPoison p1 p2)
        let qt : QTyp := ⟨r, poison, none⟩
        return { result2 with qualType := qt }
    | none => throw s!"Operation argument types do not match.\n  Left: {etyp1}\n  Op:   {op}\n  Right: {etyp2}"



termination_by fuel

/-- Rule: ref (Ott rule: ref)
-- pc ; G ; S ; L |- e : T :> p { P } -| G' ; L'
-- fresh l
-- -----------------------
-- pc ; G ; S ; L |- ref e : ref T @ l :> pc { no_pred } -| G'[l |-> T :> join pc p { P }] ; L'
-/
def typecheckNewRef (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr ctx e fuel
    let ⟨etyp, poison, pred ⟩ := result.qualType

    -- Generate fresh location (simplified)
    let (l, result') := freshTLocRes result
    let storedPoison := joinPoison ctx.pc poison
    let storedQt : QTyp := ⟨etyp, storedPoison, pred  ⟩
    let memEnv' := updateMemEnv result'.memEnv' l storedQt

    let qt : QTyp := ⟨ETyp.ref etyp l, ctx.pc, none  ⟩
    return { qualType := qt, memEnv' := memEnv', tagEnv' := result'.tagEnv', nextLoc' := result'.nextLoc', nextTag' := result'.nextTag' }
termination_by fuel

/-- Rule: assign (Ott rule: assign)
-- pc ; G ; S ; L |- e1 : ref T @ l :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T :> p'' { P'' } -| G'' ; L''
-- -----------------------
-- pc ; G ; S ; L |- e1 := e2 : unit :> join pc p' { no_pred } -| G''[l |-> T :> join pc join p' p'' { P'' }] ; L''
-/
def typecheckAssign (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, _  ⟩ := result1.qualType
    match etyp1 with
    | ETyp.ref t l =>
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
      let result2 ← typecheckExpr ctx' e2 fuel
      let ⟨etyp2, p2, pred2  ⟩ := result2.qualType
      if etyp2 != t then throw "Type mismatch in assignment"

      let storedPoison := joinPoison ctx.pc (joinPoison p1 p2)
      let storedQt : QTyp := ⟨t, storedPoison, pred2  ⟩
      let memEnv' := updateMemEnv result2.memEnv' l storedQt

      let resultPoison := joinPoison ctx.pc p1
      let qt : QTyp := ⟨ETyp.unit, resultPoison, none  ⟩
      return { qualType := qt, memEnv' := memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag'  }
    | _ => throw "Left operand of assignment must be a reference"
termination_by fuel

/-- Rules: deref_* (Ott rules: deref_poisoned, deref_no_pred, deref_guard_true, deref_guard_false, deref_guard_unknown)
--/
def typecheckDeref (ctx : TypeContext) (e : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result ← typecheckExpr ctx e fuel
    let ⟨etyp, poison, _pred ⟩ := result.qualType
    match etyp with
    | ETyp.ref t l =>
      -- Check if reference itself is poisoned
      if poison then
        -- Reference is poisoned: always return poisoned with no predicate
        -- Ott rule: deref_poisoned
        let qt : QTyp := ⟨t, true, none  ⟩  -- poisoned, no_pred
        return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
      else
        -- Reference is clean: proceed with normal predicate handling
        match result.memEnv'.get? l with
        | some ⟨etyp', p2, tp ⟩ =>
          match tp with
          | none =>  -- Ott rule: deref_no_pred
            if etyp' != t then throw s!"Type mismatch in dereference: {repr etyp'} != {repr t}"
            let poison := joinPoison ctx.pc p2
            let qt : QTyp := ⟨t, poison, none  ⟩
            return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
          | some ⟨k, arg_name, pred_body, var_env⟩ =>  -- Ott rule: deref_guard_true, deref_guard_false, deref_guard_unknown
            if etyp' != t then throw "Type mismatch in dereference"
            match result.tagEnv'.get? k with
            | some true =>
              -- Ott rule: deref_guard_true
              let poison := ctx.pc
              let qt : QTyp := ⟨t, poison, none  ⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
            | some false =>
              -- Ott rule: deref_guard_false
              let qt : QTyp := ⟨t, true, none  ⟩  -- poisoned
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
            | none =>
              -- Ott rule: deref_guard_unknown
              let poison := joinPoison ctx.pc p2
              let qt : QTyp := ⟨t, poison, some ⟨k, arg_name, pred_body, var_env⟩ ⟩
              return { qualType := qt, memEnv' := result.memEnv', tagEnv' := result.tagEnv', nextLoc' := result.nextLoc', nextTag' := result.nextTag' }
        | none => throw s!"Location {l} not found in memory environment"
    | _ => throw "Operand of dereference must be a reference"
termination_by fuel

/-- Rule: seq (Ott rule: seq)
-- pc ; G ; S ; L |- e1 : T1 :> p' { P' } -| G' ; L'
-- pc ; G' ; S ; L' |- e2 : T2 :> p'' { P'' } -| G'' ; L''
-- --------------------------------
-- pc ; G ; S ; L |- e1 ; e2 : T2 :> join p' p'' { P'' } -| G'' ; L''
-/
def typecheckSeq (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨_etyp1, p1, _  ⟩ := result1.qualType

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
    let result2 ← typecheckExpr ctx' e2 fuel
    let ⟨etyp2, p2, pred2  ⟩ := result2.qualType

    let poison := joinPoison p1 p2
    let qt : QTyp := ⟨etyp2, poison, pred2  ⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag' }
termination_by fuel


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
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    -- Premise 1: pc ; G ; S ; L |- e1 : ST1 -> ST2 # p typing_closure ( x , e , S' ) :> p1 { P1 } -| G' ; L'
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, _p1, _pred1⟩ := result1.qualType
    match etyp1 with
    | ETyp.arrow st1 st2 _p tcl =>
      -- Premise 2: pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
      let result2 ← typecheckExpr ctx' e2 fuel
      let ⟨etyp2, p2, pred2⟩ := result2.qualType

      -- Premise 3: ST1 <: T1 (check subtyping)
      if not (isSubtype st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr result2.qualType.toTyp}"

      match tcl with
      | FnTClosure.mk x body env =>
        -- Premise 4: pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- e : T2 :> p3 { P3 } -| G''' ; L'''
        let argQt : QTyp := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        let env' := VarTypeEnv.update env x argQt
        let ctx'' := { ctx with memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv' }
        let result3 ← typecheckExpr ctx'' body fuel
        let ⟨etyp3, p3, pred3⟩ := result3.qualType

        -- Premise 5: ST2 <: T2 (check subtyping)
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr result3.qualType.toTyp}"

        -- Conclusion: pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨etyp3, poison, pred3⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv', nextLoc' := result3.nextLoc', nextTag' := result3.nextTag' }
    | ETyp.parrow st1 st2 _p tcl =>
      -- Premise 2: pc ; G' ; S ; L' |- e2 : T1 :> p2 { P2 } -| G'' ; L''
      let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }
      let result2 ← typecheckExpr ctx' e2 fuel
      let ⟨etyp2, p2, pred2⟩ := result2.qualType

      -- Premise 3: ST1 <: T1 (check subtyping)
      if not (isSubtype st1 result2.qualType) then
        throw s!"Type mismatch in function application: parameter type {repr st1} is not compatible with argument type {repr result2.qualType.toTyp}"

      match tcl with
      | PFnTClosure.mk x body env =>
        -- Premise 4: pc ; G'' ; S'[x |-> T1 :> join pc p2 { P2 }] ; L'' |- pe : T2 :> p3 { P3 } -| G''' ; L'''
        let argQt : QTyp := ⟨etyp2, joinPoison ctx.pc p2, pred2⟩
        let env' := VarTypeEnv.update env x argQt
        let ctx'' := { ctx with memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv' }
        let result3 ← typecheckExpr ctx'' (body.toExpr) fuel
        let ⟨etyp3, p3, pred3⟩ := result3.qualType

        -- Premise 5: ST2 <: T2 (check subtyping)
        if not (isSubtype st2 result3.qualType) then
          throw s!"Type mismatch in function application: return type {repr st2} is not compatible with body type {repr result3.qualType.toTyp}"

        -- Conclusion: pc ; G ; S ; L |- e1 e2 : T2 :> join pc p3 { P3 } -| G''' ; L'''
        let poison := joinPoison ctx.pc p3
        let qt : QTyp := ⟨etyp3, poison, pred3⟩
        return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv', nextLoc' := result3.nextLoc', nextTag' := result3.nextTag' }

    | _ => throw "Left operand of application must be a function"
termination_by fuel


/-- Rule: let (Ott rule: let)
-- pc ; G ; S ; L |- e1 : T :> p1 { P1 } -| G' ; L'
-- pc ; G' ; S[x |-> T :> join pc p1 { P1 }] ; L' |- e2 : T2 :> p2 { P2 } -| G'' ; L''
-- ----------------------------------------------------------------------
-- pc ; G ; S ; L |- let x : T = e1 in e2 : T2 :> join pc join p1 p2 { P2 } -| G'' ; L''
-/
def typecheckVlet (ctx : TypeContext) (x : Name) (e1 : Expr) (e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p1, pred1  ⟩ := result1.qualType

    let varPoison := joinPoison ctx.pc p1
    let varQt : QTyp := ⟨etyp1, varPoison, pred1  ⟩
    let varEnv' := ctx.varEnv.update x varQt
    let ctx' := { ctx with memEnv := result1.memEnv', varEnv := varEnv', tagEnv := result1.tagEnv' }

    let result2 ← typecheckExpr ctx' e2 fuel
    let ⟨etyp2, p2, pred2  ⟩ := result2.qualType

    let poison := joinPoison ctx.pc (joinPoison p1 p2)
    let qt : QTyp := ⟨etyp2, poison, pred2  ⟩
    return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag' }
termination_by fuel


/-- Rule: if_depoison and if_std (Ott rules: if_depoison when matchGuard succeeds, if_std when it fails)
-- First tries predicate-based de-poisoning, falls back to standard conditional typing
--/
def typecheckIf (ctx : TypeContext) (e1 e2 e3 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p', _  ⟩ := result1.qualType
    if etyp1 != ETyp.bool then throw "Condition of if must be bool"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }

    -- Try predicate-based de-poisoning first
    match matchGuard e1 result1.memEnv' ctx.varEnv with
    | .ok k => do
      -- Predicate-based case (if_depoison)

      -- Type check both branches with updated tag environment
      let ctxTrue := { ctx' with tagEnv := ctx'.tagEnv.insert k true }
      let ctxFalse := { ctx' with tagEnv := ctx'.tagEnv.insert k false }

      let result2 ← typecheckExpr ctxTrue e2 fuel
      let ⟨etyp2, p'', _  ⟩ := result2.qualType

      let result3 ← typecheckExpr ctxFalse e3 fuel
      let ⟨etyp3, p''', _  ⟩ := result3.qualType

      if etyp2 != etyp3 then throw "Branches of if must have same type"

      let poison := joinPoison ctx.pc (joinPoison p'' p''')
      let qt : QTyp := ⟨etyp2, poison, none  ⟩
      let memEnv' := joinMemEnvs result2.memEnv' result3.memEnv'
      let nextLoc' := max result2.nextLoc' result3.nextLoc'
      let nextTag' := max result2.nextTag' result3.nextTag'
      -- Return original tag environment (k becomes unknown after conditional)
      return { qualType := qt, memEnv' := memEnv', tagEnv' := ctx'.tagEnv, nextLoc' := nextLoc', nextTag' := nextTag' }

    | .error _ => do
    --  dbg_trace "No tag found"
      -- Standard case (if_std) - no matching predicate found
      let branchPc := joinPoison ctx.pc p'
      let ctx'' := { ctx' with pc := branchPc }

      let result2 ← typecheckExpr ctx'' e2 fuel
      let ⟨etyp2, p'', _  ⟩ := result2.qualType

      let result3 ← typecheckExpr ctx'' e3 fuel
      let ⟨etyp3, p''', _  ⟩ := result3.qualType

      if etyp2 != etyp3 then throw "Branches of if must have same type"

      let poison := joinPoison ctx.pc (joinPoison p' (joinPoison p'' p'''))
      let qt : QTyp := ⟨etyp2, poison, none  ⟩
      let memEnv' := joinMemEnvs result2.memEnv' result3.memEnv'
      let nextLoc' := max result2.nextLoc' result3.nextLoc'
      let nextTag' := max result2.nextTag' result3.nextTag'
      return { qualType := qt, memEnv' := memEnv', tagEnv' := ctx'.tagEnv, nextLoc' := nextLoc', nextTag' := nextTag' }
termination_by fuel


/-- Rule: while_depoison and while_std (Ott rules: while_depoison when matchGuard succeeds, while_std when it fails)
-- First tries predicate-based de-poisoning, falls back to standard while typing
-- Simplified implementation for termination
--/
def typecheckWhile (ctx : TypeContext) (e1 e2 : Expr) (fuel : Nat) : TypecheckM TypeResult :=
  match fuel with
  | 0 => throw "Out of fuel"
  | fuel + 1 => do
    let result1 ← typecheckExpr ctx e1 fuel
    let ⟨etyp1, p', _  ⟩ := result1.qualType
    if etyp1 != ETyp.bool then throw "Condition of while must be bool"

    let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv' }

    -- Try predicate-based de-poisoning first
    match matchGuard e1 result1.memEnv' ctx.varEnv with
    | .ok k => do
      -- Predicate-based case (while_depoison) - simplified implementation
      let branchPc := joinPoison ctx.pc p'
      let ctx'' := { ctx' with pc := branchPc }

      let result2 ← typecheckExpr ctx'' e2 fuel
      let ⟨etyp2, p'', _  ⟩ := result2.qualType
      if etyp2 != ETyp.unit then throw "Body of while must have unit type"

      -- Simplified: just return unit with combined poison
      let poison := joinPoison ctx.pc (joinPoison p' p'')
      let qt : QTyp := ⟨ETyp.unit, poison, none  ⟩
      -- Set k to false after loop (as per Ott spec)
      let tagEnv' := ctx'.tagEnv.insert k false
      return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag' }

    | .error _ => do
      -- Standard case (while_std) - no matching predicate found
      let branchPc := joinPoison ctx.pc p'
      let ctx'' := { ctx' with pc := branchPc }

      let result2 ← typecheckExpr ctx'' e2 fuel
      let ⟨etyp2, p'', _  ⟩ := result2.qualType
      if etyp2 != ETyp.unit then throw "Body of while must have unit type"

      -- Simplified: just return unit with combined poison
      let poison := joinPoison ctx.pc (joinPoison p' p'')
      let qt : QTyp := ⟨ETyp.unit, poison, none  ⟩
      return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv', nextLoc' := result2.nextLoc', nextTag' := result2.nextTag' }
termination_by fuel


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
    nextLoc := 0
    nextTag := 1
  }
  let result ← typecheck initialCtx e defaultFuel
  return result.qualType

def typecheckExprVerbose (e : Expr) : TypecheckM TypeResult := do
  let initialCtx : TypeContext := {
    pc := false  -- clean
    memEnv := {}
    varEnv := []
    tagEnv := {}
    nextLoc := 0
    nextTag := 1
  }
  typecheck initialCtx e defaultFuel


/-- Type check a program (expression) and return a human-readable result -/
def typecheckProgram (e : Expr) (verbose : Bool) : String :=
  if verbose then
   match typecheckExprVerbose e with
   | .ok result => s!"Type: {repr result.qualType} , MemoryTypeEnv : {repr result.memEnv'} , tagEnv : {repr result.tagEnv'} , nextLoc : {repr result.nextLoc'} "
   | .error msg => s!"Type error: {msg}"
   else
  match typecheckExprSimple e   with
  | .ok qualType  => s!"Type: {repr qualType}"
  | .error msg => s!"Type error: {msg}"
