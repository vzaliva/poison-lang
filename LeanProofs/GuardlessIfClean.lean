import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.Properties
import LeanProofs.LookupUpdate
import Mathlib.Tactic
import Std.Data.ExtTreeMap.Lemmas

open Std

/-- Extract the guard tag from a qualified type's predicate, if present. -/
def qtypGuardTag (qt : QTyp) : Option Tag :=
  match qt.pred with
  | Predicate.guardClosure k _ _ _ => some k
  | Predicate.guardOnly k => some k
  | Predicate.noPred => none

/-- A qualified type is guardless whenever it is clean. -/
def guardlessIfCleanQTyp (qt : QTyp) : Prop :=
  qt.poison = false → qtypGuardTag qt = none

def nonClosureQTyp (qt : QTyp) : Prop :=
  match qt.etyp with
  | ETyp.arrow _ _ _ _ => False
  | ETyp.parrow _ _ _ _ => False
  | _ => True

/-- Extract captured environments from typing closures. -/
def fnTClosureEnv : FnTClosure → CapturedVarEnv
  | FnTClosure.regular _ _ env => env
  | FnTClosure.extern _ _ _ env => env

def pfnTClosureEnv : PFnTClosure → CapturedVarEnv
  | PFnTClosure.regular _ _ env => env
  | PFnTClosure.extern _ _ env => env

mutual

inductive guardlessIfCleanQTypDeep : QTyp → Prop
| intro (qt : QTyp) :
  guardlessIfCleanQTyp qt →
  guardlessIfCleanClosureEnv qt →
  guardlessIfCleanQTypDeep qt

/-- Clean qualified types in a memory typing environment must carry no guard tags. -/
inductive guardlessIfCleanMem : MemoryTypeEnv → Prop
| intro (locs : MemoryTypeEnv) :
  (∀ {l qt}, locs.lookup l = some qt → guardlessIfCleanQTypDeep qt) →
  guardlessIfCleanMem locs

/-- Clean qualified types in a variable typing environment must carry no guard tags. -/
inductive guardlessIfCleanVars : VarTypeEnv → Prop
| intro (vars : VarTypeEnv) :
  (∀ {x qt}, vars.lookup x = some qt → guardlessIfCleanQTypDeep qt) →
  guardlessIfCleanVars vars

/-- Clean qualified types in a captured variable environment must carry no guard tags. -/
inductive guardlessIfCleanCaptured : CapturedVarEnv → Prop
| intro (vars : CapturedVarEnv) :
  (∀ {x qt}, (x, qt) ∈ vars → guardlessIfCleanQTypDeep qt) →
  guardlessIfCleanCaptured vars

inductive guardlessIfCleanClosureEnv : QTyp → Prop
| arrow (qt : QTyp) (tcls : List FnTClosure) :
  qt.etyp = ETyp.arrow _ _ _ tcls →
  (∀ tcl ∈ tcls, guardlessIfCleanCaptured (fnTClosureEnv tcl)) →
  guardlessIfCleanClosureEnv qt
| parrow (qt : QTyp) (tcls : List PFnTClosure) :
  qt.etyp = ETyp.parrow _ _ _ tcls →
  (∀ tcl ∈ tcls, guardlessIfCleanCaptured (pfnTClosureEnv tcl)) →
  guardlessIfCleanClosureEnv qt
| other (qt : QTyp) :
  nonClosureQTyp qt →
  guardlessIfCleanClosureEnv qt

end
