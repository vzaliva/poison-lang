-- Common type safety definitions for the Poison Language
--
-- This file contains shared definitions used by both Progress and Preservation
-- properties, including evaluation relations and runtime context instantiation.

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.BigStep

-- ================================================================
-- Evaluation Relations
-- ================================================================

-- Big-step termination relation to a final configuration and resulting Value
-- Note: evaluation returns EvalResult
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : Value) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure (LeanPoison.EvalResult.success c₁ out)

-- Divergence relation: program runs out of fuel
def diverges (e : Expr) (c₀ : Config) : Prop :=
  ∀ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure LeanPoison.EvalResult.outOfFuel

-- Stuck relation: program encounters a runtime error
def stuck (e : Expr) (c₀ : Config) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool) (msg : String),
    LeanPoison.beval fuel c₀ e verbose = pure (LeanPoison.EvalResult.runtimeError msg)

-- ================================================================
-- Realisation Maps and Value Typing
-- ================================================================

-- Proof-level realisation map from logical locations to concrete runtime addresses.
-- This is a proof artefact used to relate the logical locations in types to a
-- particular execution's heap layout (Issue #76).
abbrev RealizationMap := Std.HashMap Loc Address

namespace RealizationMap

  @[inline] def lookup (m : RealizationMap) (l : Loc) : Option Address :=
    m.get? l

  @[inline] def update (m : RealizationMap) (l : Loc) (a : Address) : RealizationMap :=
    m.insert l a

  /-- `m` contains a binding for `l`. -/
  def hasKey (m : RealizationMap) (l : Loc) : Prop :=
    m.contains l

  /-- `θ₁` extends `θ₀` if it agrees on all realised locations of `θ₀`. -/
  def extendsMap (θ₀ θ₁ : RealizationMap) : Prop :=
    ∀ l a, θ₀.lookup l = some a → θ₁.lookup l = some a

  /-- `θ` is injective: distinct logical locations map to distinct addresses. -/
  def isInjective (θ : RealizationMap) : Prop :=
    ∀ l₁ l₂ a, θ.lookup l₁ = some a → θ.lookup l₂ = some a → l₁ = l₂

end RealizationMap

/-- A realisation map is well-formed if it is injective.
    This predicate can be extended with additional conditions as needed (Issue #76). -/
def wfRealizationMap (θ : RealizationMap) : Prop :=
  θ.isInjective

/-- θ₁ is a well-formed extension of θ₀: it agrees on existing locations
    and preserves injectivity (if θ₀ is injective, so is θ₁).
    This captures that extending a realisation map during evaluation
    preserves well-formedness (Issue #76). -/
def wfExtendsMap (θ₀ θ₁ : RealizationMap) : Prop :=
  θ₀.extendsMap θ₁ ∧ (wfRealizationMap θ₀ → wfRealizationMap θ₁)

-- Proof-level typing relation for runtime values.
--
-- For `ref` types, the concrete address must be the realisation (via `θ`) of some
-- logical location in the `LocSet` annotation (Issue #76).
inductive valueHasETyp (θ : RealizationMap) : Value → ETyp → Prop where
  | num (n): valueHasETyp θ (Value.num n) ETyp.int
  | bool (b): valueHasETyp θ (Value.bool b) ETyp.bool
  | unit : valueHasETyp θ Value.unit ETyp.unit
  | str (s): valueHasETyp θ (Value.str s) ETyp.string
  | loc {a : Address} {t : ETyp} {ls : LocSet} {l : Loc}
      (hlookup : θ.lookup l = some a)
      (hin : l ∈ ls) :
      valueHasETyp θ (Value.loc a) (ETyp.ref t ls)
  | closure (x e env st1 st2 p tcl):
      valueHasETyp θ (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
  | peClosure (x pe env st1 st2 p tcl):
      valueHasETyp θ (Value.peClosure x pe env) (ETyp.parrow st1 st2 p tcl)

-- ================================================================
-- Runtime Context Instantiation
-- ================================================================

-- A predicate for runtime instantiating the context: values must exist for
-- every typed variable and memory must contain entries for each typed
-- location.
def runtimeInstantiatesCtx (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) : Prop :=
  (∀ l a, θ.lookup l = some a → ctx.memEnv.contains l ∧ μ.contains a) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt →
     ∃ v, ρ.lookup x = some v ∧ valueHasETyp θ v qt.etyp)

-- ================================================================
-- Helper Lemmas
-- ================================================================

-- Helper lemma: if a variable is in the typing context and runtime instantiates the context,
-- then the variable lookup returns a value with the correct enriched type
lemma var_has_correct_type (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) (θ : RealizationMap) (x : Name) (qt : QTyp) :
  wfRealizationMap θ →
  runtimeInstantiatesCtx ctx μ ρ θ →
  ctx.varEnv.lookup x = some qt →
  ∃ v, ρ.lookup x = some v ∧ valueHasETyp θ v qt.etyp := by
  intro _h_wf ⟨_, h_vars⟩ h_lookup
  obtain ⟨v, h_v, h_typ⟩ := h_vars h_lookup
  exact ⟨v, h_v, h_typ⟩
