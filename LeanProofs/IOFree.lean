-- I/O-free predicate for Poison expressions

import LeanPoison.Syntax

-- Inductive predicate: an expression is I/O-free if it can be built using only
-- permitted constructors (excluding rand, frand, printInt, printString, externs).
inductive IOFree : Expr → Prop where
  | num (n : Int) : IOFree (Expr.num n)
  | bool (b : Bool) : IOFree (Expr.bool b)
  | unit : IOFree Expr.unit
  | str (s : String) : IOFree (Expr.str s)
  | var (x : Name) : IOFree (Expr.var x)
  | op (e₁ : Expr) (o : Op) (e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.op e₁ o e₂)
  | unaryop (o : UnaryOp) (e : Expr)
      (h : IOFree e) :
      IOFree (Expr.unaryop o e)
  | ite (e₁ e₂ e₃ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) (h₃ : IOFree e₃) :
      IOFree (Expr.ite e₁ e₂ e₃)
  | kwhile (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.kwhile e₁ e₂)
  | newRef (e : Expr) (h : IOFree e) : IOFree (Expr.newRef e)
  | deref (e : Expr) (h : IOFree e) : IOFree (Expr.deref e)
  | assign (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.assign e₁ e₂)
  | seq (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.seq e₁ e₂)
  | vlet (x : Name) (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.vlet x e₁ e₂)
  | fn (arg : Name) (st1 : Typ) (body : Expr) (st2 : Typ)
      (hbody : IOFree body) :
      IOFree (Expr.fn arg st1 body st2)
  | pfn (arg : Name) (st1 : Typ) (body : Expr) (st2 : Typ)
      (hbody : IOFree body) :
      IOFree (Expr.pfn arg st1 body st2)
  | app (e₁ e₂ : Expr)
      (h₁ : IOFree e₁) (h₂ : IOFree e₂) :
      IOFree (Expr.app e₁ e₂)
  -- No cases for: rand, frand, printInt, printString,
  --               externVal, externFn, externPfn

-- Boolean version for testing and conditional compilation
def ioFree : Expr → Bool
  | Expr.num _ => true
  | Expr.bool _ => true
  | Expr.unit => true
  | Expr.str _ => true
  | Expr.var _ => true
  | Expr.op e₁ _ e₂ => ioFree e₁ && ioFree e₂
  | Expr.unaryop _ e => ioFree e
  | Expr.ite e₁ e₂ e₃ => ioFree e₁ && ioFree e₂ && ioFree e₃
  | Expr.kwhile e₁ e₂ => ioFree e₁ && ioFree e₂
  | Expr.newRef e => ioFree e
  | Expr.deref e => ioFree e
  | Expr.assign e₁ e₂ => ioFree e₁ && ioFree e₂
  | Expr.seq e₁ e₂ => ioFree e₁ && ioFree e₂
  | Expr.vlet _ e₁ e₂ => ioFree e₁ && ioFree e₂
  | Expr.fn _ _ body _ => ioFree body
  | Expr.pfn _ _ body _ => ioFree body
  | Expr.app e₁ e₂ => ioFree e₁ && ioFree e₂
  | Expr.rand _ => false
  | Expr.frand _ => false
  | Expr.printString _ => false
  | Expr.printInt _ => false
  | Expr.externVal _ _ _ => false
  | Expr.externFn _ _ _ _ => false
  | Expr.externPfn _ _ _ => false

-- Equivalence theorem
theorem ioFree_iff_IOFree (e : Expr) : ioFree e = true ↔ IOFree e := by
  constructor
  · intro h
    cases e with
    | num n => exact IOFree.num n
    | bool b => exact IOFree.bool b
    | unit => exact IOFree.unit
    | str s => exact IOFree.str s
    | var x => exact IOFree.var x
    | op e₁ o e₂ =>
        simp [ioFree] at h
        have h₁ : ioFree e₁ = true := by
          by_contra hnot
          simp [hnot] at h
        have h₂ : ioFree e₂ = true := by
          by_contra hnot
          simp [h₁, hnot] at h
        exact IOFree.op e₁ o e₂ (ioFree_iff_IOFree e₁ |>.mp h₁) (ioFree_iff_IOFree e₂ |>.mp h₂)
    | unaryop o e =>
        simp [ioFree] at h
        have h' : ioFree e = true := by
          by_contra hnot
          simp [hnot] at h
        exact IOFree.unaryop o e (ioFree_iff_IOFree e |>.mp h')
    | ite e₁ e₂ e₃ =>
        simp [ioFree] at h
        have h₁ : ioFree e₁ = true := by
          by_contra hnot
          simp [hnot] at h
        have h₂ : ioFree e₂ = true := by
          by_contra hnot
          simp [h₁, hnot] at h
        have h₃ : ioFree e₃ = true := by
          by_contra hnot
          simp [h₁, h₂, hnot] at h
        exact IOFree.ite e₁ e₂ e₃ (ioFree_iff_IOFree e₁ |>.mp h₁) (ioFree_iff_IOFree e₂ |>.mp h₂) (ioFree_iff_IOFree e₃ |>.mp h₃)
    | kwhile e₁ e₂ =>
        simp [ioFree] at h
        have h₁ : ioFree e₁ = true := by
          by_contra hnot
          simp [hnot] at h
        have h₂ : ioFree e₂ = true := by
          by_contra hnot
          simp [h₁, hnot] at h
        exact IOFree.kwhile e₁ e₂ (ioFree_iff_IOFree e₁ |>.mp h₁) (ioFree_iff_IOFree e₂ |>.mp h₂)
    | newRef e =>
        simp [ioFree] at h
        have h' : ioFree e = true := by
          by_contra hnot
          simp [hnot] at h
        exact IOFree.newRef e (ioFree_iff_IOFree e |>.mp h')
    | deref e =>
        simp [ioFree] at h
        have h' : ioFree e = true := by
          by_contra hnot
          simp [hnot] at h
        exact IOFree.deref e (ioFree_iff_IOFree e |>.mp h')
    | assign e₁ e₂ =>
        simp [ioFree] at h
        have h₁ : ioFree e₁ = true := by
          by_contra hnot
          simp [hnot] at h
        have h₂ : ioFree e₂ = true := by
          by_contra hnot
          simp [h₁, hnot] at h
        exact IOFree.assign e₁ e₂ (ioFree_iff_IOFree e₁ |>.mp h₁) (ioFree_iff_IOFree e₂ |>.mp h₂)
    | seq e₁ e₂ =>
        simp [ioFree] at h
        have h₁ : ioFree e₁ = true := by
          by_contra hnot
          simp [hnot] at h
        have h₂ : ioFree e₂ = true := by
          by_contra hnot
          simp [h₁, hnot] at h
        exact IOFree.seq e₁ e₂ (ioFree_iff_IOFree e₁ |>.mp h₁) (ioFree_iff_IOFree e₂ |>.mp h₂)
    | vlet x e₁ e₂ =>
        simp [ioFree] at h
        have h₁ : ioFree e₁ = true := by
          by_contra hnot
          simp [hnot] at h
        have h₂ : ioFree e₂ = true := by
          by_contra hnot
          simp [h₁, hnot] at h
        exact IOFree.vlet x e₁ e₂ (ioFree_iff_IOFree e₁ |>.mp h₁) (ioFree_iff_IOFree e₂ |>.mp h₂)
    | fn arg st1 body st2 =>
        simp [ioFree] at h
        have h' : ioFree body = true := by
          by_contra hnot
          simp [hnot] at h
        exact IOFree.fn arg st1 body st2 (ioFree_iff_IOFree body |>.mp h')
    | pfn arg st1 body st2 =>
        simp [ioFree] at h
        have h' : ioFree body = true := by
          by_contra hnot
          simp [hnot] at h
        exact IOFree.pfn arg st1 body st2 (ioFree_iff_IOFree body |>.mp h')
    | app e₁ e₂ =>
        simp [ioFree] at h
        have h₁ : ioFree e₁ = true := by
          by_contra hnot
          simp [hnot] at h
        have h₂ : ioFree e₂ = true := by
          by_contra hnot
          simp [h₁, hnot] at h
        exact IOFree.app e₁ e₂ (ioFree_iff_IOFree e₁ |>.mp h₁) (ioFree_iff_IOFree e₂ |>.mp h₂)
    | rand _ | frand _ | printString _ | printInt _ | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
        simp [ioFree] at h
  · intro h
    induction h with
    | num => simp [ioFree]
    | bool => simp [ioFree]
    | unit => simp [ioFree]
    | str => simp [ioFree]
    | var => simp [ioFree]
    | op _ _ _ h₁ h₂ ih₁ ih₂ => simp [ioFree, ih₁, ih₂]
    | unaryop _ _ h ih => simp [ioFree, ih]
    | ite _ _ _ h₁ h₂ h₃ ih₁ ih₂ ih₃ => simp [ioFree, ih₁, ih₂, ih₃]
    | kwhile _ _ h₁ h₂ ih₁ ih₂ => simp [ioFree, ih₁, ih₂]
    | newRef _ h ih => simp [ioFree, ih]
    | deref _ h ih => simp [ioFree, ih]
    | assign _ _ h₁ h₂ ih₁ ih₂ => simp [ioFree, ih₁, ih₂]
    | seq _ _ h₁ h₂ ih₁ ih₂ => simp [ioFree, ih₁, ih₂]
    | vlet _ _ _ h₁ h₂ ih₁ ih₂ => simp [ioFree, ih₁, ih₂]
    | fn _ _ _ _ h ih => simp [ioFree, ih]
    | pfn _ _ _ _ h ih => simp [ioFree, ih]
    | app _ _ h₁ h₂ ih₁ ih₂ => simp [ioFree, ih₁, ih₂]
