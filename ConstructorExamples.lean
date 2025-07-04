import LeanPoison.Poison
import LeanPoison.Syntax
import LeanPoison.Typecheck

-- Examples of different constructor syntaxes for QTyp and TPred

section ConstructorExamples

-- Example 1: Using anonymous constructor ⟨...⟩
def example1 : QTyp := ⟨PTyp.int, false, none⟩

-- Example 2: Using field syntax (what we tried and failed)
-- def example2 : QTyp := { ptyp := PTyp.int, poison := false, pred := none }

-- Example 3: Using explicit QTyp.mk constructor
-- def example3 : QTyp := QTyp.mk PTyp.int false none

-- Example 4: More complex example with predicate
def example4 : QTyp :=
  let tp : TPred := ⟨42, TClosure.fn_tclosure "x" (Expr.num 0) (fun _ => none)⟩
  ⟨PTyp.bool, true, some tp⟩

-- Example 5: Pattern matching on QTyp
def extractPoisonAnon (qt : QTyp) : Poison :=
  match qt with
  | ⟨_, poison, _⟩ => poison

-- Example 6: Using accessor functions (if they exist)
def extractPoisonAccessor (qt : QTyp) : Poison :=
  qt.poison

-- Example 7: For your specific code patterns
def typecheckIntExample (ctx : TypeContext) (n : Nat) : TypecheckM TypeResult := do
  -- Current failing code:
  -- let qt : QTyp := { ptyp := PTyp.int, poison := false, pred := none }

  -- Using anonymous constructor:
  let qt : QTyp := ⟨PTyp.int, false, none⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv }

-- Example 8: Pattern matching in let bindings
def typecheckVarExample (qt : QTyp) : Poison :=
  -- Current failing code:
  -- let { ptyp, poison, pred } := qt

  -- Using anonymous pattern:
  let ⟨ptyp, poison, pred⟩ := qt
  poison

-- Example 9: Pattern matching with field renaming
def typecheckLocationExample (qt : QTyp) : PTyp :=
  -- Current failing code:
  -- let { ptyp, poison := _p, pred } := qt

  -- Using anonymous pattern:
  let ⟨ptyp, _p, pred⟩ := qt
  ptyp

-- Example 10: Creating TPred
def createTPredExample : TPred :=
  -- Using anonymous constructor:
  ⟨0, TClosure.fn_tclosure "x" (Expr.num 0) (fun _ => none)⟩

-- Example 11: Complex pattern matching
def complexPatternMatch (result : TypeResult) : PTyp :=
  -- Current failing code:
  -- let { ptyp := ptyp1, poison := p1, pred := _ } := result.qualType

  -- Using anonymous pattern with explicit binding:
  let ⟨ptyp1, p1, _⟩ := result.qualType
  ptyp1

end ConstructorExamples
