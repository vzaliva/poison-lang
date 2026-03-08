/-
  Auto-extracted from FaultRobustnessProofs.lean during StepFR operator refactor.
-/
import LeanProofs.StepFR

open List
open List.Mem
open Std
open scoped MemoryTypeEnv

lemma stepFR_kwhile
  (ctxᵢ : TypeContext) (predSat : PredSat) (tm : TagMeaning)
  (e1 e2 : Expr) (fuel' : Nat) (res : TypeResult)
  (IH : StepFR_IH predSat tm (Nat.succ (Nat.succ fuel')))
  (htc : typecheck .ioFree ctxᵢ (Expr.kwhile e1 e2) (Nat.succ (Nat.succ fuel')) = .ok res) :
  StepFR .ioFree ctxᵢ (Expr.kwhile e1 e2) res predSat tm := by
  sorry
