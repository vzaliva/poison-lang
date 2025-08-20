import Std.Data.HashMap
import LeanPoison.Syntax
open Std

-- Memory: location → value (Storing integers)
abbrev Memory := HashMap Address Int

-- Empty environments
def emptyMemory : Memory := HashMap.emptyWithCapacity 0

def emptyVarEnv : VarEnv := []

-- Environment operations
def Memory.update (m : Memory) (loc : Nat) (val : Int) : Memory :=
  m.insert loc val

def VarEnv.update (env : VarEnv) (var : Name) (val : Value) : VarEnv :=
   (var,val)::env


def VarEnv.get (env : VarEnv) (var : Name) : Option Value :=
  env.lookup var


-- Configuration for operational semantics
structure Config where
  memory : Memory
  varEnv : VarEnv  -- List (Name × Value)
  nextLoc : Address  -- for fresh location generation

-- Allocate a fresh location and return it along with updated config
def freshLoc (config : Config) : Address × Config :=
  (config.nextLoc, { config with nextLoc := config.nextLoc + 1 })

-- Manual Repr instance for Config
instance : Repr Config where
  reprPrec c _ := s!"(Config {repr c.memory} <varEnv> {repr c.varEnv})"

instance : Repr Memory where
  reprPrec m _ := repr (m.toList : List (Address × Int))

-- Repr instance for varEnv
instance : Repr VarEnv where
  reprPrec venv _ := repr (venv)

-- ToString instance for Memory
instance : ToString Memory where
  toString m := s!"{m.toList}"

-- ToString instance for config
instance : ToString Config where
  toString config := toString config.memory ++ toString config.varEnv ++ toString config.nextLoc
