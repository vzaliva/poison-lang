import Std.Data.ExtTreeMap
import Std.Data.HashMap
import LeanPoison.Syntax
open Std

-- Memory: location → value (Storing integers)
abbrev Memory := ExtTreeMap Address Int

namespace Memory

  @[inline] def lookup (m : Memory) (a : Address) : Option Int :=
    m.get? a

  @[inline] def update (m : Memory) (a : Address) (v : Int) : Memory :=
    m.insert a v

  /-- `m` contains a binding for `a`. -/
  def hasKey (m : Memory) (a : Address) : Prop :=
    m.contains a

  instance : BEq Memory where
    beq m₁ m₂ := (ExtTreeMap.toList m₁) == (ExtTreeMap.toList m₂)

end Memory

-- Empty environments
def emptyMemory : Memory := ({} : ExtTreeMap Address Int)

def emptyVarEnv : VarEnv := []

namespace VarEnv

-- helper function to lookup a variable in the variable typing environment
@[inline] def lookup (env : VarEnv) (x : Name) : Option Value :=
  List.lookup x env

-- helper function to update a variable in the variable typing environment the
-- implementation is not very efficient as mappings with existing keys are just
-- added to the front of the list. However this is sound, as lookupVarEnv always
-- returns the first mapping with a given key.
@[inline] def update (env : VarEnv) (x : Name) (v : Value) : VarEnv :=
  (x, v) :: env

/-- `env` contains a binding for `x`. -/
def hasKey (env : VarEnv) (x : Name) : Prop :=
  env.lookup x ≠ none

end VarEnv

-- ----------------------------------------------------------------------------
-- FFI runtime support (see `doc/ffi-runtime-design.md`).
-- ----------------------------------------------------------------------------

/-- Errors surfaced by the extern dispatcher. All five cases travel through
    `EvalResult.runtimeError` with a formatted message; no new top-level
    result case is introduced. -/
inductive ExternError where
  | missing              (id : ExternId)
  | kindMismatch         (id : ExternId)
  | nestedReturnMismatch (id : ExternId)
  | shapeMismatch        (id : ExternId)
  | implFailure          (id : ExternId) (msg : String)

/-- Human-readable formatter for extern errors, used by `beval` when
    lifting an `ExternError` into `EvalResult.runtimeError`. -/
def ExternError.format : ExternError → String
  | .missing id              => s!"extern id {id} not registered"
  | .kindMismatch id         => s!"extern id {id} kind mismatch"
  | .nestedReturnMismatch id => s!"extern id {id} nested return mismatch"
  | .shapeMismatch id        => s!"extern id {id} value shape mismatch"
  | .implFailure id m        => s!"extern id {id} impl failure: {m}"

/-- Lean-side implementation of one extern declaration. The three variants
    correspond exactly to the three extern declaration kinds. Functions are
    opaque (no `Repr`/`BEq`). -/
inductive ExternImpl where
  /-- Registered value for an `extern val @id`. Returned directly (and
      shape-checked against the declared `Typ`) on dispatch. -/
  | val : Value → ExternImpl
  /-- Pure extern: receives the unified runtime env (captured env plus the
      current argument binding), the current argument value, and a read-only
      view of memory. May not allocate or mutate. -/
  | pfn : (VarEnv → Value → Memory → Except ExternError Value) → ExternImpl
  /-- Impure extern: as `pfn`, but additionally receives the current
      `nextAddr` cursor, and may return updated memory and cursor along with
      the value. -/
  | fn  : (VarEnv → Value → Memory → Address →
            Except ExternError (Value × Memory × Address)) → ExternImpl

/-- Flat, globally-keyed registry: one entry per extern id covering both
    top-level and nested callable externs. Built once by the driver
    (`Main.lean`) before evaluation starts. -/
abbrev ExternRegistry := Std.HashMap ExternId ExternImpl

/-- Canonical empty registry, useful as a placeholder in proof-side `Config`
    literals that do not reason about specific extern dispatch. -/
def emptyExternRegistry : ExternRegistry := Std.HashMap.emptyWithCapacity

/-- Driver-side uniqueness check: rejects a second registration under an
    already-used extern id. -/
def register (reg : ExternRegistry) (id : ExternId) (impl : ExternImpl)
    : Except String ExternRegistry :=
  if reg.contains id then
    .error s!"extern id {id} already registered"
  else
    .ok (reg.insert id impl)

/-- Runtime shape check mapping value constructors to first-order `Typ`
    cases. Used on extern call entry (argument check), on extern call exit
    for simple returns, and on `extern val` dispatch. Does not inspect
    predicates or effects — poison lives only in the typing layer. -/
def valueMatchesTyp : Value → Typ → Bool
  | .num _,   .int      => true
  | .bool _,  .bool     => true
  | .unit,    .unit     => true
  | .str _,   .string   => true
  | .loc _,   .ref .int => true
  | _, _                => false

/-- Validate an extern call's returned value against the outermost return
    descriptor `retSpec`.

    * For `ExternReturn.simple typ _ _`, succeeds iff the value matches
      `typ` via `valueMatchesTyp`; otherwise `ExternError.shapeMismatch id`.
    * For a nested return, accepts only the exact extern-closure wrapper
      whose embedded AST matches the nested descriptor verbatim (argument
      name, identifier, argument type, inner return, and — for `nestedFn`
      — effects). Any mismatch produces `ExternError.nestedReturnMismatch id`.

    `id` is the identifier of the extern whose return is being validated
    (used only for the error report). -/
def validateExternReturn (id : ExternId) (retSpec : ExternReturn) (v : Value)
    : Except ExternError Value :=
  match retSpec, v with
  | ExternReturn.simple typ _ _, _ =>
      if valueMatchesTyp v typ then .ok v
      else .error (.shapeMismatch id)
  | ExternReturn.nestedFn innerId innerArg innerArgTyp innerRet innerEffects,
    Value.closure valArgName valBody _ =>
      if valArgName == innerArg &&
         beqExpr valBody
           (Expr.externFn innerId innerArg innerArgTyp innerRet innerEffects)
      then .ok v
      else .error (.nestedReturnMismatch id)
  | ExternReturn.nestedPfn innerId innerArg innerArgTyp innerRet,
    Value.peClosure valArgName valBody _ =>
      if valArgName == innerArg &&
         beqExpr valBody
           (Expr.externPfn innerId innerArg innerArgTyp innerRet)
      then .ok v
      else .error (.nestedReturnMismatch id)
  | ExternReturn.nestedFn _ _ _ _ _, _ => .error (.nestedReturnMismatch id)
  | ExternReturn.nestedPfn _ _ _ _, _ => .error (.nestedReturnMismatch id)

-- ----------------------------------------------------------------------------

-- Configuration for operational semantics
structure Config where
  memory : Memory
  varEnv : VarEnv  -- List (Name × Value)
  nextAddr : Address  -- for fresh address generation
  pureMode : Bool   -- whether evaluation is inside a pure function body
  /-- Lean-side extern implementations (FFI). Defaults to an empty registry
      so that older proof code that builds `Config` literals without this
      field continues to type-check unchanged; production call sites (see
      `Main.lean`) supply a populated registry. -/
  registry : ExternRegistry := emptyExternRegistry

-- Allocate a fresh address and return it along with updated config
def freshAddr (config : Config) : Address × Config :=
  (config.nextAddr, { config with nextAddr := config.nextAddr + 1 })
