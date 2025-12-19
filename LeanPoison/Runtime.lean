import Std.Data.ExtTreeMap
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

  instance : Repr Memory where
    reprPrec m _ :=
      let sorted := (ExtTreeMap.toList m : List (Address × Int)).mergeSort (fun a b => a.fst < b.fst)
      repr sorted

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

-- Configuration for operational semantics
structure Config where
  memory : Memory
  varEnv : VarEnv  -- List (Name × Value)
  nextAddr : Address  -- for fresh address generation
  pureMode : Bool   -- whether evaluation is inside a pure function body

-- Allocate a fresh address and return it along with updated config
def freshAddr (config : Config) : Address × Config :=
  (config.nextAddr, { config with nextAddr := config.nextAddr + 1 })

-- Manual Repr instance for Config
instance : Repr Config where
  reprPrec c _ := s!"(Config {repr c.memory} <varEnv> {repr c.varEnv} pure={c.pureMode})"

instance : Repr Memory where
  reprPrec m _ :=
    let sorted := (m.toList : List (Address × Int)).mergeSort (fun a b => a.fst < b.fst)
    repr sorted

-- Repr instance for varEnv
instance : Repr VarEnv where
  reprPrec venv _ := repr (venv)

-- ToString instance for Memory
instance : ToString Memory where
  toString m :=
    let sorted := (m.toList : List (Address × Int)).mergeSort (fun a b => a.fst < b.fst)
    s!"{sorted}"

-- ToString instance for config
instance : ToString Config where
  toString config := toString config.memory ++ toString config.varEnv ++ toString config.nextAddr ++ s!" pure={config.pureMode}"
