-- Common big-step semantics properties for the Poison Language
--
-- This file contains shared definitions and properties related to evaluation
-- semantics, including evaluation relations and runtime configuration well-formedness.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep

open Std

-- ================================================================
-- Evaluation Relations
-- ================================================================

-- Big-step termination relation to a final configuration and resulting Value
-- Note: evaluation returns EvalResult
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure (LeanPoison.EvalResult.success c₁ out)

-- World-indexed termination (IO equality-friendly).
def terminatesToW (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (w₀ w₁ : Void IO.RealWorld),
    LeanPoison.beval fuel c₀ e verbose w₀ = EST.Out.ok (.success c₁ out) w₁

-- Divergence relation: program runs out of fuel
def diverges (e : Expr) (c₀ : Config) : Prop :=
  ∀ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure LeanPoison.EvalResult.outOfFuel

-- Stuck relation: program encounters a runtime error
def stuck (e : Expr) (c₀ : Config) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (msg : String),
    LeanPoison.beval fuel c₀ e verbose = pure (LeanPoison.EvalResult.runtimeError msg)

-- ================================================================
-- Runtime Configuration Well-formedness
-- ================================================================

/-- A runtime configuration is well-formed if all addresses in memory are below nextAddr.
    This captures that nextAddr is the "high-water mark" for allocated physical addresses,
    analogous to wfTypeContext for logical locations. -/
def wfConfig (cfg : Config) : Prop :=
  ∀ a, cfg.memory.contains a → a < cfg.nextAddr

/-- If a config is well-formed, then nextAddr is not already in memory.
    This is the key property needed to prove freshness of newly allocated addresses. -/
lemma nextAddr_not_in_memory (cfg : Config) :
    wfConfig cfg → ¬cfg.memory.contains cfg.nextAddr := by
  intro hwf hcontains
  have h := hwf cfg.nextAddr hcontains
  exact Nat.lt_irrefl cfg.nextAddr h

/-- Evaluation preserves config well-formedness: if we start from a well-formed config
    (all addresses in memory are below nextAddr), then the final config is also well-formed.
    This follows from the fact that freshAddr returns nextAddr and increments it. -/
lemma wfConfig_preserved (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ := by
  -- TODO: Prove by induction on evaluation structure.
  -- Key insight: only newRef allocates new addresses, and it uses freshAddr which
  -- returns config.nextAddr and increments it to config.nextAddr + 1.
  -- For any address a in the new memory:
  --   - If a was in old memory: a < old_nextAddr ≤ new_nextAddr
  --   - If a = old_nextAddr: a < old_nextAddr + 1 = new_nextAddr
  sorry

/-- World-indexed version of wfConfig_preserved for use in FR proofs. -/
lemma wfConfig_preservedW (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesToW e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ := by
  intro _hterm hwf₀
  -- TODO: Follows from wfConfig_preserved once that is proven.
  -- The termination witness can be converted between terminatesToW and terminatesTo.
  sorry
