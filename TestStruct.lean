import LeanPoison.Poison
import LeanPoison.Syntax

-- Test creating instances of structures defined in mutual blocks

def test1 : QTyp :=
  { ptyp := PTyp.int, poison := false, pred := none }

def test2 : QTyp :=
  ⟨PTyp.int, false, none⟩

def test3 : TPred :=
  { tag := 0, tclosure := TClosure.fn_tclosure "x" (Expr.num 0) (fun _ => none) }

def test4 : TPred :=
  ⟨0, TClosure.fn_tclosure "x" (Expr.num 0) (fun _ => none)⟩

def test5 : QTyp :=
  { ptyp := PTyp.int, poison := false, pred := none }

#check QTyp
#check QTyp.mk
#check TPred
#check TPred.mk

-- Test accessing fields
def test6 : QTyp := test1
#check test6.ptyp
#check test6.poison
#check test6.pred

-- Test pattern matching
def extractPTyp (qt : QTyp) : PTyp :=
  match qt with
  | { ptyp, poison, pred } => ptyp

def extractPTyp2 (qt : QTyp) : PTyp :=
  qt.ptyp
