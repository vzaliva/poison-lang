import Std.Data.HashMap
import LeanPoison.Syntax
open Std

-- Memory: location → value (only natural numbers can be stored)
abbrev Memory := HashMap Nat Nat

-- Empty environments
def emptyMemory : Memory := HashMap.emptyWithCapacity 0

def emptyVarEnv : VarEnv := fun _ => none

-- Environment operations
def Memory.update (m : Memory) (loc : Nat) (val : Nat) : Memory :=
  m.insert loc val

def VarEnv.update (env : VarEnv) (var : String) (val : Value) : VarEnv :=
  fun y => if y = var then some val else env y

-- Configuration for operational semantics
structure Config where
  memory : Memory
  varEnv : VarEnv  -- Use function type to match closures
  nextLoc : Nat  -- for fresh location generation

-- Manual Repr instance for Config
instance : Repr Config where
  reprPrec c _ := s!"(Config {repr c.memory} <varEnv> {c.nextLoc})"

instance : Repr Memory where
  reprPrec m _ := repr (m.toList : List (Nat × Nat))

-- ToString instance for Memory
instance : ToString Memory where
  toString m := s!"{m.toList}"
