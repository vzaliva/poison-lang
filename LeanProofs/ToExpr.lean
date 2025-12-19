-- Formal properties of the poison language: toExpr_toPExpr

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Equality
import LeanProofs.IOHelpers
import Mathlib.Data.Nat.Basic  -- for Nat.strong_induction_on
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

import Init.Data.List
import Init.Data.List.Lemmas
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Lemmas

open Std

theorem toExpr_toPExpr (pe : PExpr) :
  pe.toExpr.toPExpr = Except.ok pe := by
  induction pe with
  | unit | num _ | bool _ | str _ | var _ =>
    simp [PExpr.toExpr, Expr.toPExpr, pure, Except.pure]
  | vlet x e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | app e1 e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | op e1 o e2 IH1 IH2 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2]
  | unaryop opname e IH =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, IH]
  | ite e1 e2 e3 IH1 IH2 IH3 =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, Seq.seq, Except.bind, IH1, IH2, IH3]
  | deref e IH =>
    simp [PExpr.toExpr, Expr.toPExpr, Functor.map, Except.map, IH]
