-- Low-level semantic definitions for the Poison Language
--
-- This file contains the foundational definitions used by both
-- `SemanticsProperties.lean` (proof bodies for evaluation invariants) and
-- `ExternRuntime.lean` (runtime extern event predicates).
--
-- Definitions only — no proof bodies beyond trivial corollaries of `wfConfig`.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Aux

open Std
open LeanPoison

-- ================================================================
-- Evaluation Relations
-- ================================================================

/-- Big-step termination relation to a final configuration and resulting Value.
    Evaluation returns `EvalResult` (pure, no IO). -/
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : Value): Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = LeanPoison.EvalResult.success c₁ out

/-- Divergence relation: program raises a runtime error. -/
def stuck (e : Expr) (c₀ : Config)  : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (msg : String),
    LeanPoison.beval fuel c₀ e verbose = LeanPoison.EvalResult.runtimeError msg

-- ================================================================
-- Runtime Configuration Well-formedness
-- ================================================================

mutual
  /-- A runtime value is well-formed w.r.t. a bound on addresses. -/
  inductive wfValue (next : Address) : Value → Prop
    | num (n : Int) : wfValue next (Value.num n)
    | bool (b : Bool) : wfValue next (Value.bool b)
    | unit : wfValue next Value.unit
    | str (s : String) : wfValue next (Value.str s)
    | loc {a : Address} : a < next → wfValue next (Value.loc a)
    | closure (x : Name) (e : Expr) (env : VarEnv) :
        wfVarEnv next env → wfValue next (Value.closure x e env)
    | peClosure (x : Name) (e : Expr) (env : VarEnv) :
        wfVarEnv next env → wfValue next (Value.peClosure x e env)

  /-- A runtime variable environment is well-formed if all stored values are. -/
  inductive wfVarEnv (next : Address) : VarEnv → Prop
    | nil : wfVarEnv next []
    | cons (x : Name) (v : Value) (env : VarEnv) :
        wfValue next v → wfVarEnv next env → wfVarEnv next ((x, v) :: env)
end

/-- An address is *reserved* by the registry when some extern entry exposes it
    as a stored location value `.val (Value.loc a)`.  Reserved addresses name
    concrete runtime cells the registry hands out (e.g. the `errno` cell), so the
    address cursor must account for them just as it accounts for memory keys. -/
def ReservedAddr (reg : ExternRegistry) (a : Address) : Prop :=
  ∃ id, reg.get? id = some (ExternImpl.val (Value.loc a))

/-- Registry/cursor compatibility: every registry-reserved address is below the
    address cursor `next`.  Kept *separate* from `wfConfig` for now (which stays
    registry-agnostic — see the `wfConfig` note below) and consumed only via the
    standalone witness `wfValue_loc_of_RegistryReservedBelow`.  The registry is
    fixed across evaluation and `nextAddr` only grows, so this invariant is
    preserved automatically (see `RegistryReservedBelow_mono`).  Folding it into
    `wfConfig` is the eventual target, deferred until a `.val` extern is actually
    trusted; see `doc/extern-write-effects.md`. -/
def RegistryReservedBelow (reg : ExternRegistry) (next : Address) : Prop :=
  ∀ a, ReservedAddr reg a → a < next

/-- `RegistryReservedBelow` is monotone in the address cursor: raising the cursor
    preserves the invariant.  With the registry fixed, this is the only fact
    needed to re-establish the invariant under `nextAddr` monotonicity. -/
theorem RegistryReservedBelow_mono {reg : ExternRegistry} {n n' : Address}
    (h : RegistryReservedBelow reg n) (hle : n ≤ n') :
    RegistryReservedBelow reg n' :=
  fun a ha => Nat.lt_of_lt_of_le (h a ha) hle

/-- The empty registry reserves no addresses, so `RegistryReservedBelow` holds
    vacuously at any cursor.  Used for throwaway configs that carry the default
    (empty) registry. -/
theorem RegistryReservedBelow_emptyExternRegistry (n : Address) :
    RegistryReservedBelow emptyExternRegistry n := by
  intro a ⟨id, hid⟩
  simp [emptyExternRegistry] at hid

/-- Registry-reserved-cell well-formedness: every registry-reserved address is
    present in memory and below the address cursor.  This is the standalone
    config-indexed predicate of doc/extern-write-effects.md — deliberately NOT
    folded into `wfConfig` (which stays registry-agnostic; see the note there).
    Both conjuncts are monotone along evaluation: memory only inserts/updates
    and `nextAddr` only grows, so `RegistryReservedWF_mono` re-establishes the
    invariant across any evaluation prefix. -/
def RegistryReservedWF (reg : ExternRegistry) (μ : Memory) (next : Address) : Prop :=
  ∀ a, ReservedAddr reg a → μ.contains a ∧ a < next

theorem RegistryReservedWF.toBelow {reg : ExternRegistry} {μ : Memory} {next : Address}
    (h : RegistryReservedWF reg μ next) : RegistryReservedBelow reg next :=
  fun a ha => (h a ha).2

/-- Monotonicity along evaluation: a memory that preserves containment and a
    non-decreasing cursor keep the reserved cells well-formed. -/
theorem RegistryReservedWF_mono {reg : ExternRegistry} {μ μ' : Memory} {n n' : Address}
    (h : RegistryReservedWF reg μ n)
    (hmem : ∀ a, μ.contains a → μ'.contains a)
    (hle : n ≤ n') :
    RegistryReservedWF reg μ' n' :=
  fun a ha => ⟨hmem a (h a ha).1, Nat.lt_of_lt_of_le (h a ha).2 hle⟩

/-- The empty registry reserves nothing. -/
theorem RegistryReservedWF_emptyExternRegistry (μ : Memory) (n : Address) :
    RegistryReservedWF emptyExternRegistry μ n := by
  intro a ⟨id, hid⟩
  simp [emptyExternRegistry] at hid

/-- A runtime configuration is well-formed if:
    (1) all addresses in memory are below nextAddr, and
    (2) all values in varEnv only reference addresses below nextAddr.
    This captures that nextAddr is the "high-water mark" for allocated physical addresses,
    analogous to wfTypeContext for logical locations.

    Note: `wfConfig` is deliberately registry-agnostic — it does not read
    `cfg.registry`.  The FR proof stack relies on this to coerce `wfConfig` freely
    across configs that differ only in their registry field.  The
    registry-reserved-address invariant (`RegistryReservedBelow`) is therefore
    kept *separate* from `wfConfig` for now; see
    `wfValue_loc_of_RegistryReservedBelow` and `doc/extern-write-effects.md`. -/
def wfConfig (cfg : Config) : Prop :=
  (∀ a, cfg.memory.contains a → a < cfg.nextAddr) ∧
  wfVarEnv cfg.nextAddr cfg.varEnv

/-- If a config is well-formed, then nextAddr is not already in memory.
    This is the key property needed to prove freshness of newly allocated addresses. -/
lemma nextAddr_not_in_memory (cfg : Config) :
    wfConfig cfg → ¬cfg.memory.contains cfg.nextAddr := by
  intro hwf hcontains
  have h := hwf.1 cfg.nextAddr hcontains
  exact Nat.lt_irrefl cfg.nextAddr h

/-- Provability witness for the registry-reserved-address mechanism.

    If a registry reserves address `a` (exposes it as a stored `.val (Value.loc a)`
    entry) and the cursor `n` bounds every reserved address, then `Value.loc a` is
    well formed at `n`.  This is exactly the step a future `val`-clause bridge needs
    to discharge `wfValue cfg.nextAddr (Value.loc a)` for a trusted `.val` extern
    such as `errno`.

    It is stated standalone, taking `RegistryReservedBelow reg n` as an explicit
    hypothesis rather than reading it out of `wfConfig`, precisely so the global
    `wfConfig` can stay registry-agnostic (folding `RegistryReservedBelow` into
    `wfConfig` would break the FR stack's registry-agnostic config coercions).
    See `doc/extern-write-effects.md`. -/
theorem wfValue_loc_of_RegistryReservedBelow
    {reg : ExternRegistry} {n a : Address} {id : ExternId}
    (hbelow : RegistryReservedBelow reg n)
    (hlookup : reg.get? id = some (ExternImpl.val (Value.loc a))) :
    wfValue n (Value.loc a) :=
  wfValue.loc (hbelow a ⟨id, hlookup⟩)
