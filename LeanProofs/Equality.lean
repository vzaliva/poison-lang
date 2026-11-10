-- Equality proofs for Poison language types
-- LawfulBEq and DecidableEq instances (for the BEq instances defined in
-- `LeanPoison/Syntax.lean`) and their supporting proofs
--
-- ============================================================================
-- API Overview
-- ============================================================================
--
-- **Public API (accessible from other files):**
--   All typeclass instances are public and provide the complete interface:
--   - `LawfulBEq` instances for: LocSet, Typ, Op, UnaryOp, PExpr, EffectTarget,
--     CaptureTarget, SyntaxPredicate, Effect, ExternReturn, Expr, Value, ETyp,
--     FnTClosure, PFnTClosure, Predicate, QTyp
--   - `DecidableEq` instances for: LocSet, ETyp, FnTClosure, PFnTClosure,
--     Predicate, QTyp
--   - `beqETypSignature_refl`: reflexivity of signature-based `ETyp` equality
--
--   Users access equality properties through the instances:
--   - Soundness: `LawfulBEq.eq_of_beq` proves `(a == b) = true → a = b`
--   - Reflexivity: `LawfulBEq.rfl` proves `(a == a) = true`
--
-- **Private Implementation (internal to this file):**
--   The proofs supporting the instances are private implementation details:
--   - Reflexivity theorems: `*_refl` (prove `beq x x = true`)
--   - Soundness theorems: `*_sound` (prove `(x == y) = true → x = y`)
--
-- ============================================================================
-- Proof Structure
-- ============================================================================
--
-- For each type, we prove:
--   1. Reflexivity: `beq x x = true` (private theorem `*_refl`)
--   2. Soundness: `(x == y) = true → x = y` (private theorem `*_sound`)
--   3. Lawfulness: Combine into `LawfulBEq` instance (public)
--
-- The `LawfulBEq` typeclass requires both properties, ensuring that boolean
-- equality is sound (only equal values compare to true) and reflexive (every
-- value compares equal to itself).
--
-- ============================================================================
-- Design note: why not `deriving DecidableEq`?
-- ============================================================================
--
-- These instances are written by hand rather than synthesized via
-- `deriving DecidableEq`, for two structural reasons:
--   1. `LocSet` is an `ExtTreeSet` (a quotient-backed set); the deriving
--      handler cannot synthesize structural equality through that field.
--   2. `Expr`/`Value` are mutually recursive, and the `DecidableEq` deriving
--      handler does not support deriving across a mutual block.
-- Both force the manual BEq/LawfulBEq + DecidableEq route taken below; this note
-- exists to prevent re-attempting `deriving` and rediscovering the obstruction.

import Mathlib
import Std.Data.ExtTreeSet.Lemmas
import LeanPoison.Syntax

open Std

-- ============================================================================
-- Proofs for types defined in LeanPoison/Syntax.lean
-- ============================================================================


private theorem LocSet.beq_refl (ls : LocSet) : BEq.beq ls ls = true := by
  -- Reduce to list reflexivity on the underlying toList representation
  have h : (ExtTreeSet.toList ls == ExtTreeSet.toList ls) = true :=
    ReflBEq.rfl (a := ExtTreeSet.toList ls)
  simpa [BEq.beq] using h

private theorem LocSet.sound (a b : LocSet) : BEq.beq a b = true → a = b := by
  intro h
  have hList : ExtTreeSet.toList a = ExtTreeSet.toList b := by
    have h' : (ExtTreeSet.toList a == ExtTreeSet.toList b) = true := by
      simpa [BEq.beq] using h
    exact LawfulBEq.eq_of_beq (a := ExtTreeSet.toList a) (b := ExtTreeSet.toList b) h'
  exact (ExtTreeSet.toList_inj (t₁ := a) (t₂ := b)).1 hList

instance : LawfulBEq LocSet where
  eq_of_beq {a b} := LocSet.sound a b
  rfl {a} := LocSet.beq_refl a

instance : DecidableEq LocSet := fun a b =>
  decidable_of_iff (a == b) ⟨LocSet.sound a b, fun h => h ▸ LocSet.beq_refl a⟩

-- Typ reflexivity proof
private theorem Typ_beq_refl (t : Typ) : BEq.beq t t = true := by
  -- We prove reflexivity by structural induction on t
  induction t with
  | int | bool | unit | string =>
    -- Base cases: same constructor compares to true
    -- Unfold BEq.beq to Typ.beq, which reduces to true by definition
    rfl
  | ref t' IH =>
    -- For ref: BEq.beq (Typ.ref t') (Typ.ref t') = Typ.beq (ref t') (ref t')
    --                                              = Typ.beq t' t'
    --                                              = true (by IH)
    simp only [BEq.beq, Typ.beq]
    exact IH
  | arrow t1 t2 IH1 IH2 =>
    -- For arrow: BEq.beq (Typ.arrow t1 t2) (Typ.arrow t1 t2)
    --          = Typ.beq (arrow t1 t2) (arrow t1 t2)
    --          = Typ.beq t1 t1 && Typ.beq t2 t2
    --          = true && true (by IH1 and IH2)
    --          = true
    simp only [BEq.beq, Typ.beq]
    -- Goal: (Typ.beq t1 t1 && Typ.beq t2 t2) = true
    -- IH1: BEq.beq t1 t1 = true, IH2: BEq.beq t2 t2 = true
    -- Unfold BEq.beq in IH1 and IH2 to get them in terms of Typ.beq
    simp only [BEq.beq] at IH1 IH2
    rw [IH1, IH2]
    rfl

-- Typ soundness proof
private theorem Typ_beq_sound (a b : Typ) : (a == b) = true → a = b := by
  intro h
  induction a generalizing b with
  | int =>
    cases b <;> simp only [BEq.beq, Typ.beq] at h <;> try contradiction
    case int => rfl
  | bool =>
    cases b <;> simp only [BEq.beq, Typ.beq] at h <;> try contradiction
    case bool => rfl
  | unit =>
    cases b <;> simp only [BEq.beq, Typ.beq] at h <;> try contradiction
    case unit => rfl
  | string =>
    cases b <;> simp only [BEq.beq, Typ.beq] at h <;> try contradiction
    case string => rfl
  | ref t' IH =>
    cases b <;> simp only [BEq.beq, Typ.beq] at h <;> try contradiction
    case ref t'' =>
      have : t' = t'' := IH t'' h
      subst this
      rfl
  | arrow t1 t2 IH1 IH2 =>
    cases b <;> simp only [BEq.beq, Typ.beq] at h <;> try contradiction
    case arrow t1' t2' =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have : t1 = t1' := IH1 t1' h1
      have : t2 = t2' := IH2 t2' h2
      subst_vars
      rfl

-- LawfulBEq instance for Typ
instance : LawfulBEq Typ where
  eq_of_beq {a b} := Typ_beq_sound a b
  rfl {a} := Typ_beq_refl a

-- LawfulBEq instances for Op and UnaryOp (derived BEq is lawful for enums)
instance : LawfulBEq Op where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> (try contradiction) <;> rfl
  rfl {a} := by cases a <;> rfl

instance : LawfulBEq UnaryOp where
  eq_of_beq {a b} h := by
    cases a; cases b; rfl
  rfl {a} := by cases a; rfl

-- ============================================================================
-- PExpr: Reflexivity, Soundness, and LawfulBEq instance
-- ============================================================================
-- PExpr only depends on Op and UnaryOp, so it comes before Expr

-- Reflexivity proof for beqPExpr
private theorem beqPExpr_refl (e : PExpr) : beqPExpr e e = true := by
  induction e with
  | unit => rfl
  | num n => simp [beqPExpr]
  | bool b => simp [beqPExpr]
  | str s => simp [beqPExpr]
  | var x => simp [beqPExpr]
  | op e1 op e2 IH1 IH2 =>
      simp [beqPExpr, IH1, IH2]
  | unaryop op e IH =>
      simp [beqPExpr, IH]
  | ite e1 e2 e3 IH1 IH2 IH3 =>
      simp [beqPExpr, IH1, IH2, IH3]
  | deref e IH =>
      simp [beqPExpr, IH]
  | vlet x e1 e2 IH1 IH2 =>
      simp [beqPExpr, IH1, IH2]
  | app e1 e2 IH1 IH2 =>
      simp [beqPExpr, IH1, IH2]

-- Soundness proof for beqPExpr
private theorem beqPExpr_sound (a b : PExpr) : (a == b) = true → a = b := by
  intro h
  induction a generalizing b with
  | unit =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h
      all_goals (try contradiction)
      case unit => rfl
  | num n1 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h
      all_goals (try contradiction)
      case num n2 => have : n1 = n2 := of_decide_eq_true h; subst this; rfl
  | bool b1 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h
      all_goals (try contradiction)
      case bool b2 => have : b1 = b2 := of_decide_eq_true h; subst this; rfl
  | str s1 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h
      all_goals (try contradiction)
      case str s2 => have : s1 = s2 := of_decide_eq_true h; subst this; rfl
  | var x1 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h
      all_goals (try contradiction)
      case var x2 => have : x1 = x2 := of_decide_eq_true h; subst this; rfl
  | op e1 op1 e2 IH1 IH2 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h <;> try contradiction
      case op e1' op2 e2' =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h_op, h_e1⟩, h_e2⟩ := h
        have : op1 = op2 := eq_of_beq h_op
        have : e1 = e1' := IH1 e1' h_e1
        have : e2 = e2' := IH2 e2' h_e2
        subst_vars; rfl
  | unaryop op1 e1 IH =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h <;> try contradiction
      case unaryop op2 e2 =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨h_op, h_e⟩ := h
        have : op1 = op2 := eq_of_beq h_op
        have : e1 = e2 := IH e2 h_e
        subst_vars; rfl
  | ite e1 e2 e3 IH1 IH2 IH3 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h <;> try contradiction
      case ite e1' e2' e3' =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h_e1, h_e2⟩, h_e3⟩ := h
        have : e1 = e1' := IH1 e1' h_e1
        have : e2 = e2' := IH2 e2' h_e2
        have : e3 = e3' := IH3 e3' h_e3
        subst_vars; rfl
  | deref e1 IH =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h <;> try contradiction
      case deref e2 => have : e1 = e2 := IH e2 h; subst this; rfl
  | vlet x1 e1 e2 IH1 IH2 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h <;> try contradiction
      case vlet x2 e1' e2' =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h_x, h_e1⟩, h_e2⟩ := h
        have : x1 = x2 := of_decide_eq_true h_x
        have : e1 = e1' := IH1 e1' h_e1
        have : e2 = e2' := IH2 e2' h_e2
        subst_vars; rfl
  | app e1 e2 IH1 IH2 =>
      cases b <;> simp only [BEq.beq, beqPExpr] at h <;> try contradiction
      case app e1' e2' =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨h_e1, h_e2⟩ := h
        have : e1 = e1' := IH1 e1' h_e1
        have : e2 = e2' := IH2 e2' h_e2
        subst_vars; rfl


-- LawfulBEq instance for PExpr
instance : LawfulBEq PExpr where
  eq_of_beq {a b} := beqPExpr_sound a b
  rfl {a} := beqPExpr_refl a

-- ============================================================================
-- EffectTarget, CaptureTarget: Reflexivity, Soundness, and LawfulBEq instances
-- ============================================================================

private theorem EffectTarget_beq_refl (t : EffectTarget) : (t == t) = true := by
  cases t with
  | namedVar x =>
      simp only [BEq.beq]
      have : decide (x = x) = true := decide_eq_true rfl
      exact this

private theorem EffectTarget_beq_sound (a b : EffectTarget) : (a == b) = true → a = b := by
  intro h
  cases a; cases b; simp only [BEq.beq] at h
  case namedVar.namedVar x1 x2 =>
    have : x1 = x2 := of_decide_eq_true h
    subst this
    rfl

instance : LawfulBEq EffectTarget where
  eq_of_beq {a b} := EffectTarget_beq_sound a b
  rfl {a} := EffectTarget_beq_refl a

private theorem CaptureTarget_beq_refl (t : CaptureTarget) : (t == t) = true := by
  cases t with
  | bareVar x => simp only [BEq.beq]; exact decide_eq_true rfl
  | memVar x => simp only [BEq.beq]; exact decide_eq_true rfl

private theorem CaptureTarget_beq_sound (a b : CaptureTarget) : (a == b) = true → a = b := by
  intro h
  cases a <;> cases b <;> simp only [BEq.beq] at h <;> try contradiction
  case bareVar.bareVar x1 x2 => have : x1 = x2 := of_decide_eq_true h; subst this; rfl
  case memVar.memVar x1 x2 => have : x1 = x2 := of_decide_eq_true h; subst this; rfl

instance : LawfulBEq CaptureTarget where
  eq_of_beq {a b} := CaptureTarget_beq_sound a b
  rfl {a} := CaptureTarget_beq_refl a

-- ============================================================================
-- Expr, SyntaxPredicate, Effect, Capture, ExternReturn: Mutual recursion
-- ============================================================================
-- These types are mutually recursive with each other in LeanPoison/Syntax.lean.
-- We define all reflexivity and soundness proofs together using well-founded recursion.

-- Reflexivity proofs using well-founded recursion
mutual
  private theorem beqExpr_refl : ∀ (e : Expr), beqExpr e e = true
    | Expr.unit => rfl
    | Expr.num n => decide_eq_true rfl
    | Expr.bool b => decide_eq_true rfl
    | Expr.str s => decide_eq_true rfl
    | Expr.var x => decide_eq_true rfl
    | Expr.op e1 op e2 =>
        show (beqExpr e1 e1 && op == op && beqExpr e2 e2) = true from by
          rw [beqExpr_refl e1, beqExpr_refl e2]; simp
    | Expr.unaryop op e =>
        show (op == op && beqExpr e e) = true from by
          rw [beqExpr_refl e]; simp
    | Expr.ite e1 e2 e3 =>
        show (beqExpr e1 e1 && beqExpr e2 e2 && beqExpr e3 e3) = true from by
          rw [beqExpr_refl e1, beqExpr_refl e2, beqExpr_refl e3]; rfl
    | Expr.newRef e => beqExpr_refl e
    | Expr.assign e1 e2 =>
        show (beqExpr e1 e1 && beqExpr e2 e2) = true from by
          rw [beqExpr_refl e1, beqExpr_refl e2]; rfl
    | Expr.deref e => beqExpr_refl e
    | Expr.seq e1 e2 =>
        show (beqExpr e1 e1 && beqExpr e2 e2) = true from by
          rw [beqExpr_refl e1, beqExpr_refl e2]; rfl
    | Expr.vlet x e1 e2 =>
        show (x == x && beqExpr e1 e1 && beqExpr e2 e2) = true from by
          rw [beqExpr_refl e1, beqExpr_refl e2]; simp
    | Expr.fn x t1 e t2 =>
        show (x == x && (t1 == t1) && beqExpr e e && (t2 == t2)) = true from by
          rw [beqExpr_refl e, Typ_beq_refl t1, Typ_beq_refl t2]; simp
    | Expr.pfn x t1 e t2 =>
        show (x == x && (t1 == t1) && beqExpr e e && (t2 == t2)) = true from by
          rw [beqExpr_refl e, Typ_beq_refl t1, Typ_beq_refl t2]; simp
    | Expr.app e1 e2 =>
        show (beqExpr e1 e1 && beqExpr e2 e2) = true from by
          rw [beqExpr_refl e1, beqExpr_refl e2]; rfl
    | Expr.externVal id typ poison pred =>
        show (id == id && typ == typ && poison == poison && beqSyntaxPredicate pred pred) = true from by
          rw [Typ_beq_refl typ, beqSyntaxPredicate_refl pred]; simp
    | Expr.externRef id refPoison refPred cellPoison cellPred =>
        show (id == id && refPoison == refPoison && beqSyntaxPredicate refPred refPred
              && cellPoison == cellPoison && beqSyntaxPredicate cellPred cellPred) = true from by
          rw [beqSyntaxPredicate_refl refPred, beqSyntaxPredicate_refl cellPred]; simp
    | Expr.externFn id arg argTyp argPoison argPred retSpec effects cap =>
        show (id == id && arg == arg && argTyp == argTyp && argPoison == argPoison && beqSyntaxPredicate argPred argPred && beqExternReturn retSpec retSpec && beqEffectList effects effects && beqCaptureList cap cap) = true from by
          rw [Typ_beq_refl argTyp, beqSyntaxPredicate_refl argPred, beqExternReturn_refl retSpec, beqEffectList_refl effects, beqCaptureList_refl cap]; simp
    | Expr.externPfn id arg argTyp argPoison argPred retSpec cap =>
        show (id == id && arg == arg && argTyp == argTyp && argPoison == argPoison && beqSyntaxPredicate argPred argPred && beqExternReturn retSpec retSpec && beqCaptureList cap cap) = true from by
          rw [Typ_beq_refl argTyp, beqSyntaxPredicate_refl argPred, beqExternReturn_refl retSpec, beqCaptureList_refl cap]; simp

  private theorem beqSyntaxPredicate_refl : ∀ (p : SyntaxPredicate), beqSyntaxPredicate p p = true
    | SyntaxPredicate.guardClosure tag arg body => by
        have heq : beqSyntaxPredicate (.guardClosure tag arg body) (.guardClosure tag arg body) =
                   (tag == tag && arg == arg && beqExpr body body) := rfl
        rw [heq, beqExpr_refl body]
        simp
    | SyntaxPredicate.guardOnly tag => by
        have heq : beqSyntaxPredicate (.guardOnly tag) (.guardOnly tag) = (tag == tag) := rfl
        rw [heq]; simp
    | SyntaxPredicate.noPred =>
        rfl

  private theorem beqEffect_refl : ∀ (e : Effect), beqEffect e e = true
    | ⟨target, poison, pred⟩ => by
        have heq : beqEffect ⟨target, poison, pred⟩ ⟨target, poison, pred⟩ =
                   (target == target && poison == poison && beqSyntaxPredicate pred pred) := rfl
        rw [heq, EffectTarget_beq_refl target, beqSyntaxPredicate_refl pred]
        simp

  private theorem beqEffectList_refl : ∀ (es : List Effect), beqEffectList es es = true
    | [] => rfl
    | e :: es' => by
        have heq : beqEffectList (e :: es') (e :: es') = (beqEffect e e && beqEffectList es' es') := rfl
        rw [heq, beqEffect_refl e, beqEffectList_refl es']
        rfl

  private theorem beqCapture_refl : ∀ (c : Capture), beqCapture c c = true
    | ⟨target, typ, poison, pred⟩ => by
        have heq : beqCapture ⟨target, typ, poison, pred⟩ ⟨target, typ, poison, pred⟩ =
                   (target == target && typ == typ && poison == poison && beqSyntaxPredicate pred pred) := rfl
        rw [heq, CaptureTarget_beq_refl target, Typ_beq_refl typ, beqSyntaxPredicate_refl pred]
        simp

  private theorem beqCaptureList_refl : ∀ (cs : List Capture), beqCaptureList cs cs = true
    | [] => rfl
    | c :: cs' => by
        have heq : beqCaptureList (c :: cs') (c :: cs') = (beqCapture c c && beqCaptureList cs' cs') := rfl
        rw [heq, beqCapture_refl c, beqCaptureList_refl cs']
        rfl

  private theorem beqExternReturn_refl : ∀ (r : ExternReturn), beqExternReturn r r = true
    | ExternReturn.simple typ poison pred => by
        have heq : beqExternReturn (.simple typ poison pred) (.simple typ poison pred) =
                   ((typ == typ) && poison == poison && beqSyntaxPredicate pred pred) := rfl
        have h_typ : (typ == typ) = true := Typ_beq_refl typ
        rw [heq, h_typ, beqSyntaxPredicate_refl pred]
        simp
    | ExternReturn.nestedFn id x typ argPoison argPred ret eff cap => by
        have heq : beqExternReturn (.nestedFn id x typ argPoison argPred ret eff cap) (.nestedFn id x typ argPoison argPred ret eff cap) =
                   (id == id && x == x && (typ == typ) && argPoison == argPoison && beqSyntaxPredicate argPred argPred && beqExternReturn ret ret && beqEffectList eff eff && beqCaptureList cap cap) := rfl
        have h_typ : (typ == typ) = true := Typ_beq_refl typ
        rw [heq, h_typ, beqSyntaxPredicate_refl argPred, beqExternReturn_refl ret, beqEffectList_refl eff, beqCaptureList_refl cap]
        simp
    | ExternReturn.nestedPfn id x typ argPoison argPred ret cap => by
        have heq : beqExternReturn (.nestedPfn id x typ argPoison argPred ret cap) (.nestedPfn id x typ argPoison argPred ret cap) =
                   (id == id && x == x && (typ == typ) && argPoison == argPoison && beqSyntaxPredicate argPred argPred && beqExternReturn ret ret && beqCaptureList cap cap) := rfl
        have h_typ : (typ == typ) = true := Typ_beq_refl typ
        rw [heq, h_typ, beqSyntaxPredicate_refl argPred, beqExternReturn_refl ret, beqCaptureList_refl cap]
        simp
end

-- Soundness proofs using well-founded recursion
mutual
  -- beqExpr_sound with all cases explicitly handled
  private theorem beqExpr_sound : ∀ (a b : Expr), beqExpr a b = true → a = b
    | Expr.unit, Expr.unit => fun _ => rfl
    | Expr.num n1, Expr.num n2 => fun h => by
        -- beqExpr matches already
        have : n1 = n2 := of_decide_eq_true h
        subst this; rfl
    | Expr.bool b1, Expr.bool b2 => fun h => by
        -- beqExpr matches already
        have : b1 = b2 := of_decide_eq_true h
        subst this; rfl
    | Expr.str s1, Expr.str s2 => fun h => by
        -- beqExpr matches already
        have : s1 = s2 := of_decide_eq_true h
        subst this; rfl
    | Expr.var x1, Expr.var x2 => fun h => by
        -- beqExpr matches already
        have : x1 = x2 := of_decide_eq_true h
        subst this; rfl
    | Expr.op e1 op1 e2, Expr.op e1' op2 e2' => fun h => by
        have heq : beqExpr (.op e1 op1 e2) (.op e1' op2 e2') =
                   (beqExpr e1 e1' && (op1 == op2) && beqExpr e2 e2') := rfl
        rw [heq, Bool.and_eq_true, Bool.and_eq_true] at h
        obtain ⟨⟨h_e1, h_op⟩, h_e2⟩ := h
        have : e1 = e1' := beqExpr_sound e1 e1' h_e1
        have : op1 = op2 := eq_of_beq h_op
        have : e2 = e2' := beqExpr_sound e2 e2' h_e2
        subst_vars; rfl
    | Expr.unaryop op1 e1, Expr.unaryop op2 e2 => fun h => by
        have heq : beqExpr (.unaryop op1 e1) (.unaryop op2 e2) =
                   ((op1 == op2) && beqExpr e1 e2) := rfl
        rw [heq, Bool.and_eq_true] at h
        obtain ⟨h_op, h_e⟩ := h
        have : op1 = op2 := eq_of_beq h_op
        have : e1 = e2 := beqExpr_sound e1 e2 h_e
        subst_vars; rfl
    | Expr.ite e1 e2 e3, Expr.ite e1' e2' e3' => fun h => by
        have heq : beqExpr (.ite e1 e2 e3) (.ite e1' e2' e3') =
                   (beqExpr e1 e1' && beqExpr e2 e2' && beqExpr e3 e3') := rfl
        rw [heq, Bool.and_eq_true, Bool.and_eq_true] at h
        obtain ⟨⟨h_e1, h_e2⟩, h_e3⟩ := h
        have : e1 = e1' := beqExpr_sound e1 e1' h_e1
        have : e2 = e2' := beqExpr_sound e2 e2' h_e2
        have : e3 = e3' := beqExpr_sound e3 e3' h_e3
        subst_vars; rfl
    | Expr.newRef e1, Expr.newRef e2 => fun h => by
        -- beqExpr matches already
        have : e1 = e2 := beqExpr_sound e1 e2 h
        subst this; rfl
    | Expr.assign e1 e2, Expr.assign e1' e2' => fun h => by
        have heq : beqExpr (.assign e1 e2) (.assign e1' e2') =
                   (beqExpr e1 e1' && beqExpr e2 e2') := rfl
        rw [heq, Bool.and_eq_true] at h
        obtain ⟨h_e1, h_e2⟩ := h
        have : e1 = e1' := beqExpr_sound e1 e1' h_e1
        have : e2 = e2' := beqExpr_sound e2 e2' h_e2
        subst_vars; rfl
    | Expr.deref e1, Expr.deref e2 => fun h => by
        -- beqExpr matches already
        have : e1 = e2 := beqExpr_sound e1 e2 h
        subst this; rfl
    | Expr.seq e1 e2, Expr.seq e1' e2' => fun h => by
        have heq : beqExpr (.seq e1 e2) (.seq e1' e2') =
                   (beqExpr e1 e1' && beqExpr e2 e2') := rfl
        rw [heq, Bool.and_eq_true] at h
        obtain ⟨h_e1, h_e2⟩ := h
        have : e1 = e1' := beqExpr_sound e1 e1' h_e1
        have : e2 = e2' := beqExpr_sound e2 e2' h_e2
        subst_vars; rfl
    | Expr.vlet x1 e1 e2, Expr.vlet x2 e1' e2' => fun h => by
        have heq : beqExpr (.vlet x1 e1 e2) (.vlet x2 e1' e2') =
                   (x1 == x2 && beqExpr e1 e1' && beqExpr e2 e2') := rfl
        rw [heq, Bool.and_eq_true, Bool.and_eq_true] at h
        obtain ⟨⟨h_x, h_e1⟩, h_e2⟩ := h
        have : x1 = x2 := of_decide_eq_true h_x
        have : e1 = e1' := beqExpr_sound e1 e1' h_e1
        have : e2 = e2' := beqExpr_sound e2 e2' h_e2
        subst_vars; rfl
    | Expr.fn x1 t1 e1 t1', Expr.fn x2 t2 e2 t2' => fun h => by
        have heq : beqExpr (.fn x1 t1 e1 t1') (.fn x2 t2 e2 t2') =
                   (x1 == x2 && Typ.beq t1 t2 && beqExpr e1 e2 && Typ.beq t1' t2') := rfl
        rw [heq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
        obtain ⟨⟨⟨h_x, h_t1⟩, h_e⟩, h_t2⟩ := h
        have : x1 = x2 := of_decide_eq_true h_x
        have : t1 = t2 := Typ_beq_sound t1 t2 h_t1
        have : e1 = e2 := beqExpr_sound e1 e2 h_e
        have : t1' = t2' := Typ_beq_sound t1' t2' h_t2
        subst_vars; rfl
    | Expr.pfn x1 t1 e1 t1', Expr.pfn x2 t2 e2 t2' => fun h => by
        have heq : beqExpr (.pfn x1 t1 e1 t1') (.pfn x2 t2 e2 t2') =
                   (x1 == x2 && Typ.beq t1 t2 && beqExpr e1 e2 && Typ.beq t1' t2') := rfl
        rw [heq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
        obtain ⟨⟨⟨h_x, h_t1⟩, h_e⟩, h_t2⟩ := h
        have : x1 = x2 := of_decide_eq_true h_x
        have : t1 = t2 := Typ_beq_sound t1 t2 h_t1
        have : e1 = e2 := beqExpr_sound e1 e2 h_e
        have : t1' = t2' := Typ_beq_sound t1' t2' h_t2
        subst_vars; rfl
    | Expr.app e1 e2, Expr.app e1' e2' => fun h => by
        have heq : beqExpr (.app e1 e2) (.app e1' e2') =
                   (beqExpr e1 e1' && beqExpr e2 e2') := rfl
        rw [heq, Bool.and_eq_true] at h
        obtain ⟨h_e1, h_e2⟩ := h
        have : e1 = e1' := beqExpr_sound e1 e1' h_e1
        have : e2 = e2' := beqExpr_sound e2 e2' h_e2
        subst_vars; rfl
    | Expr.externVal id1 typ1 poison1 pred1, Expr.externVal id2 typ2 poison2 pred2 => fun h => by
        change (id1 == id2 && typ1 == typ2 && poison1 == poison2 && beqSyntaxPredicate pred1 pred2) = true at h
        rw [Bool.and_eq_true] at h; obtain ⟨h_left, h_pred⟩ := h
        rw [Bool.and_eq_true] at h_left; obtain ⟨h_left2, h_poison⟩ := h_left
        rw [Bool.and_eq_true] at h_left2; obtain ⟨h_id, h_typ⟩ := h_left2
        have : id1 = id2 := of_decide_eq_true h_id
        have : typ1 = typ2 := Typ_beq_sound typ1 typ2 h_typ
        have : poison1 = poison2 := of_decide_eq_true h_poison
        have : pred1 = pred2 := beqSyntaxPredicate_sound pred1 pred2 h_pred
        subst_vars; rfl
    | Expr.externRef id1 rp1 rpred1 cp1 cpred1, Expr.externRef id2 rp2 rpred2 cp2 cpred2 => fun h => by
        change (id1 == id2 && rp1 == rp2 && beqSyntaxPredicate rpred1 rpred2
                && cp1 == cp2 && beqSyntaxPredicate cpred1 cpred2) = true at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨h_id, h_rp⟩, h_rpred⟩, h_cp⟩, h_cpred⟩ := h
        have : id1 = id2 := of_decide_eq_true h_id
        have : rp1 = rp2 := of_decide_eq_true h_rp
        have : rpred1 = rpred2 := beqSyntaxPredicate_sound rpred1 rpred2 h_rpred
        have : cp1 = cp2 := of_decide_eq_true h_cp
        have : cpred1 = cpred2 := beqSyntaxPredicate_sound cpred1 cpred2 h_cpred
        subst_vars; rfl
    | Expr.externFn id1 arg1 argTyp1 argPoison1 argPred1 retSpec1 effects1 cap1, Expr.externFn id2 arg2 argTyp2 argPoison2 argPred2 retSpec2 effects2 cap2 => fun h => by
        change (id1 == id2 && arg1 == arg2 && argTyp1 == argTyp2 && argPoison1 == argPoison2 && beqSyntaxPredicate argPred1 argPred2 && beqExternReturn retSpec1 retSpec2 && beqEffectList effects1 effects2 && beqCaptureList cap1 cap2) = true at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨h_id, h_arg⟩, h_typ⟩, h_ap⟩, h_sp⟩, h_ret⟩, h_eff⟩, h_cap⟩ := h
        have : id1 = id2 := of_decide_eq_true h_id
        have : arg1 = arg2 := of_decide_eq_true h_arg
        have : argTyp1 = argTyp2 := Typ_beq_sound argTyp1 argTyp2 h_typ
        have : argPoison1 = argPoison2 := of_decide_eq_true h_ap
        have : argPred1 = argPred2 := beqSyntaxPredicate_sound argPred1 argPred2 h_sp
        have : retSpec1 = retSpec2 := beqExternReturn_sound retSpec1 retSpec2 h_ret
        have : effects1 = effects2 := beqEffectList_sound effects1 effects2 h_eff
        have : cap1 = cap2 := beqCaptureList_sound cap1 cap2 h_cap
        subst_vars; rfl
    | Expr.externPfn id1 arg1 argTyp1 argPoison1 argPred1 retSpec1 cap1, Expr.externPfn id2 arg2 argTyp2 argPoison2 argPred2 retSpec2 cap2 => fun h => by
        change (id1 == id2 && arg1 == arg2 && argTyp1 == argTyp2 && argPoison1 == argPoison2 && beqSyntaxPredicate argPred1 argPred2 && beqExternReturn retSpec1 retSpec2 && beqCaptureList cap1 cap2) = true at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨h_id, h_arg⟩, h_typ⟩, h_ap⟩, h_sp⟩, h_ret⟩, h_cap⟩ := h
        have : id1 = id2 := of_decide_eq_true h_id
        have : arg1 = arg2 := of_decide_eq_true h_arg
        have : argTyp1 = argTyp2 := Typ_beq_sound argTyp1 argTyp2 h_typ
        have : argPoison1 = argPoison2 := of_decide_eq_true h_ap
        have : argPred1 = argPred2 := beqSyntaxPredicate_sound argPred1 argPred2 h_sp
        have : retSpec1 = retSpec2 := beqExternReturn_sound retSpec1 retSpec2 h_ret
        have : cap1 = cap2 := beqCaptureList_sound cap1 cap2 h_cap
        subst_vars; rfl
    -- All mismatched constructor pairs return contradiction
    | .unit, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .num _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .bool _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .str _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .var _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .externRef _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externRef _ _ _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    -- Remaining mismatched constructor wildcards
    | .unit, .num _ => fun h => by have : false = true := h; contradiction
    | .unit, .bool _ => fun h => by have : false = true := h; contradiction
    | .unit, .str _ => fun h => by have : false = true := h; contradiction
    | .unit, .var _ => fun h => by have : false = true := h; contradiction
    | .unit, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .newRef _ => fun h => by have : false = true := h; contradiction
    | .unit, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .deref _ => fun h => by have : false = true := h; contradiction
    | .unit, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .app _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unit, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .unit => fun h => by have : false = true := h; contradiction
    | .num _, .bool _ => fun h => by have : false = true := h; contradiction
    | .num _, .str _ => fun h => by have : false = true := h; contradiction
    | .num _, .var _ => fun h => by have : false = true := h; contradiction
    | .num _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .num _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .deref _ => fun h => by have : false = true := h; contradiction
    | .num _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .num _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .unit => fun h => by have : false = true := h; contradiction
    | .bool _, .num _ => fun h => by have : false = true := h; contradiction
    | .bool _, .str _ => fun h => by have : false = true := h; contradiction
    | .bool _, .var _ => fun h => by have : false = true := h; contradiction
    | .bool _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .bool _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .deref _ => fun h => by have : false = true := h; contradiction
    | .bool _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .bool _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .unit => fun h => by have : false = true := h; contradiction
    | .str _, .num _ => fun h => by have : false = true := h; contradiction
    | .str _, .bool _ => fun h => by have : false = true := h; contradiction
    | .str _, .var _ => fun h => by have : false = true := h; contradiction
    | .str _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .str _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .deref _ => fun h => by have : false = true := h; contradiction
    | .str _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .str _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .unit => fun h => by have : false = true := h; contradiction
    | .var _, .num _ => fun h => by have : false = true := h; contradiction
    | .var _, .bool _ => fun h => by have : false = true := h; contradiction
    | .var _, .str _ => fun h => by have : false = true := h; contradiction
    | .var _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .var _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .deref _ => fun h => by have : false = true := h; contradiction
    | .var _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .var _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .op _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .unit => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .unaryop _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .ite _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .unit => fun h => by have : false = true := h; contradiction
    | .newRef _, .num _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .bool _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .str _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .var _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .deref _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .newRef _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .unit => fun h => by have : false = true := h; contradiction
    | .assign _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .assign _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .unit => fun h => by have : false = true := h; contradiction
    | .deref _, .num _ => fun h => by have : false = true := h; contradiction
    | .deref _, .bool _ => fun h => by have : false = true := h; contradiction
    | .deref _, .str _ => fun h => by have : false = true := h; contradiction
    | .deref _, .var _ => fun h => by have : false = true := h; contradiction
    | .deref _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .deref _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .deref _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .unit => fun h => by have : false = true := h; contradiction
    | .seq _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .seq _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .vlet _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .fn _ _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .pfn _ _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .unit => fun h => by have : false = true := h; contradiction
    | .app _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .app _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externVal _ _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externFn _ _ _ _ _ _ _ _, .externPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .unit => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .num _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .bool _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .str _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .var _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .op _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .unaryop _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .ite _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .newRef _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .assign _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .deref _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .seq _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .vlet _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .fn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .pfn _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .app _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .externVal _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .externPfn _ _ _ _ _ _ _, .externFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction

  private theorem beqSyntaxPredicate_sound : ∀ (a b : SyntaxPredicate), (a == b) = true → a = b
    | .guardClosure tag1 arg1 body1, .guardClosure tag2 arg2 body2 => fun h => by
        have heq : beqSyntaxPredicate (.guardClosure tag1 arg1 body1) (.guardClosure tag2 arg2 body2) =
                   (tag1 == tag2 && arg1 == arg2 && beqExpr body1 body2) := rfl
        simp only [BEq.beq, heq, Bool.and_eq_true] at h
        obtain ⟨⟨h_tag, h_arg⟩, h_body⟩ := h
        have : tag1 = tag2 := of_decide_eq_true h_tag
        have : arg1 = arg2 := of_decide_eq_true h_arg
        have : body1 = body2 := beqExpr_sound body1 body2 h_body
        subst_vars; rfl
    | .guardOnly tag1, .guardOnly tag2 => fun h => by
        have heq : beqSyntaxPredicate (.guardOnly tag1) (.guardOnly tag2) = (tag1 == tag2) := rfl
        simp only [BEq.beq, heq] at h
        have : tag1 = tag2 := of_decide_eq_true h
        subst this; rfl
    | .noPred, .noPred => fun _ => rfl
    -- Mismatched constructor wildcards (6 total)
    | .guardClosure _ _ _, .guardOnly _ => fun h => by have : false = true := h; contradiction
    | .guardClosure _ _ _, .noPred => fun h => by have : false = true := h; contradiction
    | .guardOnly _, .guardClosure _ _ _ => fun h => by have : false = true := h; contradiction
    | .guardOnly _, .noPred => fun h => by have : false = true := h; contradiction
    | .noPred, .guardClosure _ _ _ => fun h => by have : false = true := h; contradiction
    | .noPred, .guardOnly _ => fun h => by have : false = true := h; contradiction

  private theorem beqEffect_sound : ∀ (a b : Effect), (a == b) = true → a = b
    | ⟨target1, poison1, pred1⟩, ⟨target2, poison2, pred2⟩ => fun h => by
        have heq : beqEffect ⟨target1, poison1, pred1⟩ ⟨target2, poison2, pred2⟩ =
                   (target1 == target2 && poison1 == poison2 && beqSyntaxPredicate pred1 pred2) := rfl
        simp only [BEq.beq, heq, Bool.and_eq_true] at h
        obtain ⟨⟨h_target, h_poison⟩, h_pred⟩ := h
        have : target1 = target2 := EffectTarget_beq_sound target1 target2 h_target
        have : poison1 = poison2 := of_decide_eq_true h_poison
        have : pred1 = pred2 := beqSyntaxPredicate_sound pred1 pred2 h_pred
        subst_vars; rfl

  private theorem beqEffectList_sound : ∀ (a b : List Effect), beqEffectList a b = true → a = b
    | [], [] => fun _ => rfl
    | [], _ :: _ => fun h => by have : false = true := h; contradiction
    | _ :: _, [] => fun h => by have : false = true := h; contradiction
    | e1 :: es1, e2 :: es2 => fun h => by
        have heq : beqEffectList (e1 :: es1) (e2 :: es2) = (beqEffect e1 e2 && beqEffectList es1 es2) := rfl
        rw [heq, Bool.and_eq_true] at h
        obtain ⟨h_e, h_es⟩ := h
        have : e1 = e2 := beqEffect_sound e1 e2 h_e
        have : es1 = es2 := beqEffectList_sound es1 es2 h_es
        subst_vars; rfl

  private theorem beqCapture_sound : ∀ (a b : Capture), beqCapture a b = true → a = b
    | ⟨target1, typ1, poison1, pred1⟩, ⟨target2, typ2, poison2, pred2⟩ => fun h => by
        have heq : beqCapture ⟨target1, typ1, poison1, pred1⟩ ⟨target2, typ2, poison2, pred2⟩ =
                   (target1 == target2 && typ1 == typ2 && poison1 == poison2 && beqSyntaxPredicate pred1 pred2) := rfl
        rw [heq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
        obtain ⟨⟨⟨h_target, h_typ⟩, h_poison⟩, h_pred⟩ := h
        have : target1 = target2 := CaptureTarget_beq_sound target1 target2 h_target
        have : typ1 = typ2 := Typ_beq_sound typ1 typ2 h_typ
        have : poison1 = poison2 := of_decide_eq_true h_poison
        have : pred1 = pred2 := beqSyntaxPredicate_sound pred1 pred2 h_pred
        subst_vars; rfl

  private theorem beqCaptureList_sound : ∀ (a b : List Capture), beqCaptureList a b = true → a = b
    | [], [] => fun _ => rfl
    | [], _ :: _ => fun h => by have : false = true := h; contradiction
    | _ :: _, [] => fun h => by have : false = true := h; contradiction
    | c1 :: cs1, c2 :: cs2 => fun h => by
        have heq : beqCaptureList (c1 :: cs1) (c2 :: cs2) = (beqCapture c1 c2 && beqCaptureList cs1 cs2) := rfl
        rw [heq, Bool.and_eq_true] at h
        obtain ⟨h_c, h_cs⟩ := h
        have : c1 = c2 := beqCapture_sound c1 c2 h_c
        have : cs1 = cs2 := beqCaptureList_sound cs1 cs2 h_cs
        subst_vars; rfl

  private theorem beqExternReturn_sound : ∀ (a b : ExternReturn), (a == b) = true → a = b
    | .simple typ1 poison1 pred1, .simple typ2 poison2 pred2 => fun h => by
        have heq : beqExternReturn (.simple typ1 poison1 pred1) (.simple typ2 poison2 pred2) =
                   ((typ1 == typ2) && poison1 == poison2 && beqSyntaxPredicate pred1 pred2) := rfl
        simp only [BEq.beq, heq, Bool.and_eq_true] at h
        obtain ⟨⟨h_typ, h_poison⟩, h_pred⟩ := h
        have : typ1 = typ2 := Typ_beq_sound typ1 typ2 h_typ
        have : poison1 = poison2 := of_decide_eq_true h_poison
        have : pred1 = pred2 := beqSyntaxPredicate_sound pred1 pred2 h_pred
        subst_vars; rfl
    | .nestedFn id1 x1 typ1 argPoison1 argPred1 ret1 eff1 cap1, .nestedFn id2 x2 typ2 argPoison2 argPred2 ret2 eff2 cap2 => fun h => by
        have heq : beqExternReturn (.nestedFn id1 x1 typ1 argPoison1 argPred1 ret1 eff1 cap1) (.nestedFn id2 x2 typ2 argPoison2 argPred2 ret2 eff2 cap2) =
                   (id1 == id2 && x1 == x2 && (typ1 == typ2) && argPoison1 == argPoison2 && beqSyntaxPredicate argPred1 argPred2 && beqExternReturn ret1 ret2 && beqEffectList eff1 eff2 && beqCaptureList cap1 cap2) := rfl
        simp only [BEq.beq, heq, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨h_id, h_x⟩, h_typ⟩, h_ap⟩, h_sp⟩, h_ret⟩, h_eff⟩, h_cap⟩ := h
        have : id1 = id2 := of_decide_eq_true h_id
        have : x1 = x2 := of_decide_eq_true h_x
        have : typ1 = typ2 := Typ_beq_sound typ1 typ2 h_typ
        have : argPoison1 = argPoison2 := of_decide_eq_true h_ap
        have : argPred1 = argPred2 := beqSyntaxPredicate_sound argPred1 argPred2 h_sp
        have : ret1 = ret2 := beqExternReturn_sound ret1 ret2 h_ret
        have : eff1 = eff2 := beqEffectList_sound eff1 eff2 h_eff
        have : cap1 = cap2 := beqCaptureList_sound cap1 cap2 h_cap
        subst_vars; rfl
    | .nestedPfn id1 x1 typ1 argPoison1 argPred1 ret1 cap1, .nestedPfn id2 x2 typ2 argPoison2 argPred2 ret2 cap2 => fun h => by
        have heq : beqExternReturn (.nestedPfn id1 x1 typ1 argPoison1 argPred1 ret1 cap1) (.nestedPfn id2 x2 typ2 argPoison2 argPred2 ret2 cap2) =
                   (id1 == id2 && x1 == x2 && (typ1 == typ2) && argPoison1 == argPoison2 && beqSyntaxPredicate argPred1 argPred2 && beqExternReturn ret1 ret2 && beqCaptureList cap1 cap2) := rfl
        simp only [BEq.beq, heq, Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨⟨⟨h_id, h_x⟩, h_typ⟩, h_ap⟩, h_sp⟩, h_ret⟩, h_cap⟩ := h
        have : id1 = id2 := of_decide_eq_true h_id
        have : x1 = x2 := of_decide_eq_true h_x
        have : typ1 = typ2 := Typ_beq_sound typ1 typ2 h_typ
        have : argPoison1 = argPoison2 := of_decide_eq_true h_ap
        have : argPred1 = argPred2 := beqSyntaxPredicate_sound argPred1 argPred2 h_sp
        have : ret1 = ret2 := beqExternReturn_sound ret1 ret2 h_ret
        have : cap1 = cap2 := beqCaptureList_sound cap1 cap2 h_cap
        subst_vars; rfl
    -- Mismatched constructor wildcards (6 total)
    | .simple _ _ _, .nestedFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .simple _ _ _, .nestedPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .nestedFn _ _ _ _ _ _ _ _, .simple _ _ _ => fun h => by have : false = true := h; contradiction
    | .nestedFn _ _ _ _ _ _ _ _, .nestedPfn _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
    | .nestedPfn _ _ _ _ _ _ _, .simple _ _ _ => fun h => by have : false = true := h; contradiction
    | .nestedPfn _ _ _ _ _ _ _, .nestedFn _ _ _ _ _ _ _ _ => fun h => by have : false = true := h; contradiction
end

instance : LawfulBEq SyntaxPredicate where
  eq_of_beq {a b} := beqSyntaxPredicate_sound a b
  rfl {a} := beqSyntaxPredicate_refl a

instance : LawfulBEq Effect where
  eq_of_beq {a b} := beqEffect_sound a b
  rfl {a} := beqEffect_refl a

instance : LawfulBEq ExternReturn where
  eq_of_beq {a b} := beqExternReturn_sound a b
  rfl {a} := beqExternReturn_refl a

instance : LawfulBEq Expr where
  eq_of_beq {a b} := beqExpr_sound a b
  rfl {a} := beqExpr_refl a

-- ============================================================================
-- Value: Reflexivity, Soundness, and LawfulBEq instance
-- ============================================================================
-- Value depends on Expr (proven above)

-- Reflexivity proofs for Value
mutual
private theorem beqValue_refl (v : Value) : beqValue v v = true := by
  cases v with
  | num n => simp [beqValue]
  | bool b => simp [beqValue]
  | unit => simp [beqValue]
  | loc l => simp [beqValue]
  | str s => simp [beqValue]
  | closure x e env =>
      simp [beqValue, beqExpr_refl e, beqValueVarEnv_refl env]
  | peClosure x e env =>
      simp [beqValue, beqExpr_refl e, beqValueVarEnv_refl env]

private theorem beqValueVarEnv_refl : ∀ (env : VarEnv), beqValueVarEnv env env = true
  | [] => by simp [beqValueVarEnv]
  | (x, v) :: env' => by
      simp [beqValueVarEnv, beqValue_refl v, beqValueVarEnv_refl env']
end

-- Soundness proofs for Value
mutual
private theorem beqValue_sound (a b : Value) : beqValue a b = true → a = b := by
  intro h
  cases a <;> cases b <;> try (simp only [beqValue] at h; contradiction)
  case num n1 n2 =>
    simp only [beqValue] at h
    have : n1 = n2 := of_decide_eq_true h
    subst this
    rfl
  case bool b1 b2 =>
    simp only [beqValue] at h
    have : b1 = b2 := of_decide_eq_true h
    subst this
    rfl
  case unit => rfl
  case loc l1 l2 =>
    simp only [beqValue] at h
    have : l1 = l2 := of_decide_eq_true h
    subst this
    rfl
  case str s1 s2 =>
    simp only [beqValue] at h
    have : s1 = s2 := of_decide_eq_true h
    subst this
    rfl
  case closure x1 e1 env1 x2 e2 env2 =>
    simp only [beqValue, Bool.and_eq_true] at h
    obtain ⟨⟨h_x, h_e⟩, h_env⟩ := h
    have : x1 = x2 := of_decide_eq_true h_x
    have : e1 = e2 := beqExpr_sound e1 e2 h_e
    have : env1 = env2 := beqValueVarEnv_sound env1 env2 h_env
    subst_vars
    rfl
  case peClosure x1 e1 env1 x2 e2 env2 =>
    simp only [beqValue, Bool.and_eq_true] at h
    obtain ⟨⟨h_x, h_e⟩, h_env⟩ := h
    have : x1 = x2 := of_decide_eq_true h_x
    have : e1 = e2 := beqExpr_sound e1 e2 h_e
    have : env1 = env2 := beqValueVarEnv_sound env1 env2 h_env
    subst_vars
    rfl

private theorem beqValueVarEnv_sound : ∀ (a b : VarEnv), beqValueVarEnv a b = true → a = b
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp only [beqValueVarEnv] at h; contradiction
  | _ :: _, [] => fun h => by simp only [beqValueVarEnv] at h; contradiction
  | (x1, v1) :: env1, (x2, v2) :: env2 => fun h => by
      simp only [beqValueVarEnv, Bool.and_eq_true] at h
      obtain ⟨⟨h_x, h_v⟩, h_env⟩ := h
      have : x1 = x2 := of_decide_eq_true h_x
      have : v1 = v2 := beqValue_sound v1 v2 h_v
      have : env1 = env2 := beqValueVarEnv_sound env1 env2 h_env
      subst_vars
      rfl
end

-- LawfulBEq instance for Value
instance : LawfulBEq Value where
  eq_of_beq {a b} := beqValue_sound a b
  rfl {a} := beqValue_refl a

-- ============================================================================
-- ETyp, FnTClosure, PFnTClosure, Predicate, QTyp: Mutual recursion
-- ============================================================================

-- Reflexivity lemmas for mutually recursive types
-- These proofs depend on the beqExpr_refl and related proofs defined earlier.

mutual
-- Prove reflexivity of beqFnTClosureList
private theorem beqFnTClosureList_refl : ∀ (tcls : List FnTClosure), beqFnTClosureList tcls tcls = true
  | [] => by simp [beqFnTClosureList]
  | tcl :: tcls' => by
      simp [beqFnTClosureList, beqFnTClosure_refl tcl, beqFnTClosureList_refl tcls']

-- Prove reflexivity of beqPFnTClosureList
private theorem beqPFnTClosureList_refl : ∀ (tcls : List PFnTClosure), beqPFnTClosureList tcls tcls = true
  | [] => by simp [beqPFnTClosureList]
  | tcl :: tcls' => by
      simp [beqPFnTClosureList, beqPFnTClosure_refl tcl, beqPFnTClosureList_refl tcls']

-- Prove reflexivity of beqETyp using mutual induction
private theorem beqETyp_refl (t : ETyp) : beqETyp t t = true := by
  cases t with
  | int => simp [beqETyp]
  | bool => simp [beqETyp]
  | unit => simp [beqETyp]
  | string => simp [beqETyp]
  | ref l =>
      simp [beqETyp]
  | arrow t1 t2 p tcl =>
      simp [beqETyp, beqFnTClosureList_refl tcl]
  | parrow t1 t2 p tcl =>
      simp [beqETyp, beqPFnTClosureList_refl tcl]

-- Prove reflexivity of beqVarEnv
private theorem beqVarEnv_refl : ∀ (env : CapturedVarEnv), beqVarEnv env env = true
  | [] => by simp [beqVarEnv]
  | (x, qt) :: env' => by
      simp [beqVarEnv, beqQTyp_refl qt, beqVarEnv_refl env']

-- Prove reflexivity of beqPredicate
private theorem beqPredicate_refl (p : Predicate) : beqPredicate p p = true := by
  cases p with
  | guardClosure tag arg body env =>
      simp [beqPredicate, beqVarEnv_refl env]
  | guardOnly tag =>
      simp [beqPredicate]
  | noPred =>
      simp [beqPredicate]

-- Prove reflexivity of beqQTyp
private theorem beqQTyp_refl (qt : QTyp) : beqQTyp qt qt = true := by
  cases qt with
  | mk etyp poison pred =>
      simp [beqQTyp, beqETyp_refl etyp, beqPredicate_refl pred]

-- Prove reflexivity of beqFnTClosure
private theorem beqFnTClosure_refl (tcl : FnTClosure) : beqFnTClosure tcl tcl = true := by
  cases tcl with
  | regular x e env =>
      simp [beqFnTClosure, beqVarEnv_refl env]
  | extern id x retSpec effects env argQt captures =>
      simp [beqFnTClosure, beqExternReturn_refl retSpec, beqEffectList_refl effects, beqVarEnv_refl env, beqQTyp_refl argQt,
        beqCaptureList_refl captures]

-- Prove reflexivity of beqPFnTClosure
private theorem beqPFnTClosure_refl (tcl : PFnTClosure) : beqPFnTClosure tcl tcl = true := by
  cases tcl with
  | regular x e env =>
      simp [beqPFnTClosure, beqVarEnv_refl env]
  | extern id x retSpec env argQt captures =>
      simp [beqPFnTClosure, beqExternReturn_refl retSpec, beqVarEnv_refl env, beqQTyp_refl argQt,
        beqCaptureList_refl captures]

end

-- Mutual soundness proofs for ETyp and related types
mutual
-- Prove soundness of beqFnTClosureList
private theorem beqFnTClosureList_sound : ∀ (a b : List FnTClosure), beqFnTClosureList a b = true → a = b
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp only [beqFnTClosureList] at h; contradiction
  | _ :: _, [] => fun h => by simp only [beqFnTClosureList] at h; contradiction
  | tcl1 :: a', tcl2 :: b' => fun h => by
      simp only [beqFnTClosureList, Bool.and_eq_true] at h
      obtain ⟨h_tcl, h_tcls⟩ := h
      have : tcl1 = tcl2 := beqFnTClosure_sound tcl1 tcl2 h_tcl
      have : a' = b' := beqFnTClosureList_sound a' b' h_tcls
      subst_vars
      rfl

-- Prove soundness of beqPFnTClosureList
private theorem beqPFnTClosureList_sound : ∀ (a b : List PFnTClosure), beqPFnTClosureList a b = true → a = b
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp only [beqPFnTClosureList] at h; contradiction
  | _ :: _, [] => fun h => by simp only [beqPFnTClosureList] at h; contradiction
  | tcl1 :: a', tcl2 :: b' => fun h => by
      simp only [beqPFnTClosureList, Bool.and_eq_true] at h
      obtain ⟨h_tcl, h_tcls⟩ := h
      have : tcl1 = tcl2 := beqPFnTClosure_sound tcl1 tcl2 h_tcl
      have : a' = b' := beqPFnTClosureList_sound a' b' h_tcls
      subst_vars
      rfl

private theorem beqETyp_sound (a b : ETyp) : (a == b) = true → a = b := by
  intro h
  cases a <;> cases b <;> try (simp only [BEq.beq, beqETyp] at h; contradiction)
  case int.int | bool.bool | unit.unit | string.string => rfl
  case ref l1 l2 =>
    simp only [BEq.beq, beqETyp] at h
    have : l1 = l2 := LocSet.sound l1 l2 h
    subst_vars
    rfl
  case arrow st1 st2 p1 tcl1 st1' st2' p2 tcl2 =>
    simp only [BEq.beq, beqETyp, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h_st1, h_st2⟩, h_p⟩, h_tcl⟩ := h
    -- Typ uses its own beq, use the soundness theorem
    have : st1 = st1' := Typ_beq_sound st1 st1' h_st1
    have : st2 = st2' := Typ_beq_sound st2 st2' h_st2
    have : p1 = p2 := of_decide_eq_true h_p
    have : tcl1 = tcl2 := beqFnTClosureList_sound tcl1 tcl2 h_tcl
    subst_vars
    rfl
  case parrow st1 st2 p1 tcl1 st1' st2' p2 tcl2 =>
    simp only [BEq.beq, beqETyp, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h_st1, h_st2⟩, h_p⟩, h_tcl⟩ := h
    -- Typ uses its own beq, use the soundness theorem
    have : st1 = st1' := Typ_beq_sound st1 st1' h_st1
    have : st2 = st2' := Typ_beq_sound st2 st2' h_st2
    have : p1 = p2 := of_decide_eq_true h_p
    have : tcl1 = tcl2 := beqPFnTClosureList_sound tcl1 tcl2 h_tcl
    subst_vars
    rfl

private theorem beqVarEnv_sound : ∀ (a b : CapturedVarEnv), beqVarEnv a b = true → a = b
  | [], [] => fun _ => rfl
  | [], _ :: _ => fun h => by simp only [beqVarEnv] at h; contradiction
  | _ :: _, [] => fun h => by simp only [beqVarEnv] at h; contradiction
  | (x1, qt1) :: a', (x2, qt2) :: b' => fun h => by
      simp only [beqVarEnv, Bool.and_eq_true] at h
      obtain ⟨⟨h_x, h_qt⟩, h_env⟩ := h
      have : x1 = x2 := of_decide_eq_true h_x
      have : qt1 = qt2 := beqQTyp_sound qt1 qt2 h_qt
      have : a' = b' := beqVarEnv_sound a' b' h_env
      subst_vars
      rfl

private theorem beqPredicate_sound (a b : Predicate) : (a == b) = true → a = b := by
  intro h
  cases a <;> cases b
  case guardClosure.guardClosure tag1 arg1 body1 env1 tag2 arg2 body2 env2 =>
    simp only [BEq.beq, beqPredicate, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h_tag, h_arg⟩, h_body⟩, h_env⟩ := h
    have : tag1 = tag2 := of_decide_eq_true h_tag
    have : arg1 = arg2 := of_decide_eq_true h_arg
    have : body1 = body2 := beqPExpr_sound body1 body2 h_body
    have : env1 = env2 := beqVarEnv_sound env1 env2 h_env
    subst_vars
    rfl
  case guardOnly.guardOnly tag1 tag2 =>
    simp only [BEq.beq, beqPredicate] at h
    have : tag1 = tag2 := of_decide_eq_true h
    subst_vars
    rfl
  case noPred.noPred => rfl
  all_goals (
    simp only [BEq.beq, beqPredicate] at h
    -- h is now false = true, which is a contradiction
    contradiction
  )

private theorem beqQTyp_sound (a b : QTyp) : (a == b) = true → a = b := by
  intro h
  cases a with
  | mk etyp1 poison1 pred1 =>
    cases b with
    | mk etyp2 poison2 pred2 =>
      simp only [BEq.beq, beqQTyp, Bool.and_eq_true] at h
      obtain ⟨⟨h_etyp, h_poison⟩, h_pred⟩ := h
      have : etyp1 = etyp2 := beqETyp_sound etyp1 etyp2 h_etyp
      have : poison1 = poison2 := of_decide_eq_true h_poison
      have : pred1 = pred2 := beqPredicate_sound pred1 pred2 h_pred
      subst_vars
      rfl

private theorem beqFnTClosure_sound (a b : FnTClosure) : (a == b) = true → a = b := by
  intro h
  cases a with
  | regular x1 e1 env1 =>
    cases b with
    | regular x2 e2 env2 =>
      simp only [BEq.beq, beqFnTClosure] at h
      have h_and : (x1 == x2 && beqExpr e1 e2) = true ∧ beqVarEnv env1 env2 = true := by
        rw [Bool.and_eq_true] at h
        exact h
      have h_x_e : (x1 == x2) = true ∧ beqExpr e1 e2 = true := by
        rw [Bool.and_eq_true] at h_and
        exact h_and.1
      have h_x : (x1 == x2) = true := h_x_e.1
      have h_e : beqExpr e1 e2 = true := h_x_e.2
      have h_env : beqVarEnv env1 env2 = true := h_and.2
      have : x1 = x2 := of_decide_eq_true h_x
      have : e1 = e2 := beqExpr_sound e1 e2 h_e
      have : env1 = env2 := beqVarEnv_sound env1 env2 h_env
      subst_vars
      rfl
    | extern _ _ _ _ _ _ _ =>
      simp only [BEq.beq, beqFnTClosure] at h
      contradiction
  | extern id1 x1 retSpec1 eff1 env1 argQt1 cap1 =>
    cases b with
    | regular _ _ _ =>
      simp only [BEq.beq, beqFnTClosure] at h
      contradiction
    | extern id2 x2 retSpec2 eff2 env2 argQt2 cap2 =>
      simp only [BEq.beq, beqFnTClosure] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨h_id, h_x⟩, h_ret⟩, h_eff⟩, h_env⟩, h_argQt⟩, h_cap⟩ := h
      have : id1 = id2 := of_decide_eq_true h_id
      have : x1 = x2 := of_decide_eq_true h_x
      have : retSpec1 = retSpec2 := beqExternReturn_sound retSpec1 retSpec2 h_ret
      have : eff1 = eff2 := beqEffectList_sound eff1 eff2 h_eff
      have : env1 = env2 := beqVarEnv_sound env1 env2 h_env
      have : argQt1 = argQt2 := beqQTyp_sound argQt1 argQt2 h_argQt
      have : cap1 = cap2 := beqCaptureList_sound cap1 cap2 h_cap
      subst_vars
      rfl

private theorem beqPFnTClosure_sound (a b : PFnTClosure) : (a == b) = true → a = b := by
  intro h
  cases a with
  | regular x1 e1 env1 =>
    cases b with
    | regular x2 e2 env2 =>
      simp only [BEq.beq, beqPFnTClosure] at h
      have h_and : (x1 == x2 && beqPExpr e1 e2) = true ∧ beqVarEnv env1 env2 = true := by
        rw [Bool.and_eq_true] at h
        exact h
      have h_x_e : (x1 == x2) = true ∧ beqPExpr e1 e2 = true := by
        rw [Bool.and_eq_true] at h_and
        exact h_and.1
      have h_x : (x1 == x2) = true := h_x_e.1
      have h_e : beqPExpr e1 e2 = true := h_x_e.2
      have h_env : beqVarEnv env1 env2 = true := h_and.2
      have : x1 = x2 := of_decide_eq_true h_x
      have : e1 = e2 := beqPExpr_sound e1 e2 h_e
      have : env1 = env2 := beqVarEnv_sound env1 env2 h_env
      subst_vars
      rfl
    | extern _ _ _ _ _ =>
      simp only [BEq.beq, beqPFnTClosure] at h
      contradiction
  | extern id1 x1 retSpec1 env1 argQt1 cap1 =>
    cases b with
    | regular _ _ _ =>
      simp only [BEq.beq, beqPFnTClosure] at h
      contradiction
    | extern id2 x2 retSpec2 env2 argQt2 cap2 =>
      simp only [BEq.beq, beqPFnTClosure] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨⟨⟨⟨h_id, h_x⟩, h_ret⟩, h_env⟩, h_argQt⟩, h_cap⟩ := h
      have : id1 = id2 := of_decide_eq_true h_id
      have : x1 = x2 := of_decide_eq_true h_x
      have : retSpec1 = retSpec2 := beqExternReturn_sound retSpec1 retSpec2 h_ret
      have : env1 = env2 := beqVarEnv_sound env1 env2 h_env
      have : argQt1 = argQt2 := beqQTyp_sound argQt1 argQt2 h_argQt
      have : cap1 = cap2 := beqCaptureList_sound cap1 cap2 h_cap
      subst_vars
      rfl

end

-- Now we can define LawfulBEq instances, which combine soundness and reflexivity
instance : LawfulBEq ETyp where
  eq_of_beq {a b} := beqETyp_sound a b
  rfl {a} := beqETyp_refl a

instance : LawfulBEq FnTClosure where
  eq_of_beq {a b} := beqFnTClosure_sound a b
  rfl {a} := beqFnTClosure_refl a

instance : LawfulBEq PFnTClosure where
  eq_of_beq {a b} := beqPFnTClosure_sound a b
  rfl {a} := beqPFnTClosure_refl a

instance : LawfulBEq Predicate where
  eq_of_beq {a b} := beqPredicate_sound a b
  rfl {a} := beqPredicate_refl a

instance : LawfulBEq QTyp where
  eq_of_beq {a b} := beqQTyp_sound a b
  rfl {a} := beqQTyp_refl a

-- DecidableEq instances, obtained from soundness and reflexivity via decidable_of_iff
instance : DecidableEq ETyp := fun a b =>
  decidable_of_iff (a == b) ⟨beqETyp_sound a b, fun h => h ▸ beqETyp_refl a⟩

instance : DecidableEq FnTClosure := fun a b =>
  decidable_of_iff (a == b) ⟨beqFnTClosure_sound a b, fun h => h ▸ beqFnTClosure_refl a⟩

instance : DecidableEq PFnTClosure := fun a b =>
  decidable_of_iff (a == b) ⟨beqPFnTClosure_sound a b, fun h => h ▸ beqPFnTClosure_refl a⟩

instance : DecidableEq Predicate := fun a b =>
  decidable_of_iff (a == b) ⟨beqPredicate_sound a b, fun h => h ▸ beqPredicate_refl a⟩

instance : DecidableEq QTyp := fun a b =>
  decidable_of_iff (a == b) ⟨beqQTyp_sound a b, fun h => h ▸ beqQTyp_refl a⟩

-- ============================================================================
-- Signature-based equality for ETyp (beqETypSignature)
-- ============================================================================
-- Signature-based equality compares function signatures
-- (parameter type, return type, poison flag) but ignores closure contents.
-- This is used for type checking, where we need to compare function types
-- based on their signatures rather than their full structural equality.
--
-- Note: beqETypSignature is not sound for function types (two functions with
-- the same signature but different closures would be considered equal by
-- beqETypSignature but are not propositionally equal). Therefore, it cannot
-- have a full LawfulBEq instance. We only prove reflexivity here.

-- Reflexivity proof for beqETypSignature
theorem beqETypSignature_refl (t : ETyp) : beqETypSignature t t = true := by
  cases t with
  | int | bool | unit | string => simp [beqETypSignature]
  | ref l =>
      simp [beqETypSignature]
  | arrow st1 st2 p _ =>
      simp [beqETypSignature]
  | parrow st1 st2 p _ =>
      simp [beqETypSignature]
