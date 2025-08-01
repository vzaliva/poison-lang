import Std.Data.HashMap
import LeanPoison.Syntax
open Std

-- Memory: location → value (Storing integers)
abbrev Memory := HashMap Address Int

-- Empty environments
def emptyMemory : Memory := HashMap.emptyWithCapacity 0

def emptyVarEnv : VarEnv := fun _ => none

-- Environment operations
def Memory.update (m : Memory) (loc : Nat) (val : Int) : Memory :=
  m.insert loc val

def VarEnv.update (env : VarEnv) (var : String) (val : Value) : VarEnv :=
  fun y => if y = var then some val else env y

-- Configuration for operational semantics
structure Config where
  memory : Memory
  varEnv : VarEnv  -- Use function type to match closures
  nextLoc : Address  -- for fresh location generation

-- Allocate a fresh location and return it along with updated config
def freshLoc (config : Config) : Address × Config :=
  (config.nextLoc, { config with nextLoc := config.nextLoc + 1 })

-- Manual Repr instance for Config
instance : Repr Config where
  reprPrec c _ := s!"(Config {repr c.memory} <varEnv> {c.nextLoc})"

instance : Repr Memory where
  reprPrec m _ := repr (m.toList : List (Address × Int))

-- ToString instance for Memory
instance : ToString Memory where
  toString m := s!"{m.toList}"
