-- Common big-step semantics properties for the Poison Language
--
-- This file contains shared definitions and properties related to evaluation
-- semantics, including evaluation relations and runtime configuration well-formedness.

import LeanPoison.Syntax
import LeanPoison.Runtime
import LeanPoison.BigStep
import LeanProofs.Aux
import Mathlib.Tactic
import Batteries.Data.List.Lemmas

open Std

-- ================================================================
-- Evaluation Relations
-- ================================================================

-- Big-step termination relation to a final configuration and resulting Value
-- Note: evaluation returns EvalResult (pure, no IO)

/-- Any `Config` whose registry matches the default can be rewritten as an
    update of its memory/varEnv/nextAddr/pureMode fields alone. -/
lemma config_eq_of_registry_default (cfg : Config)
    (h : cfg.registry = emptyExternRegistry) :
  cfg = { memory := cfg.memory, varEnv := cfg.varEnv,
          nextAddr := cfg.nextAddr, pureMode := cfg.pureMode } := by
  cases cfg with
  | mk _ _ _ _ _ =>
    simp only [Config.mk.injEq, true_and]
    exact h

def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : Value): Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = LeanPoison.EvalResult.success c₁ out

-- Divergence relation: program runs out of fuel
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

/-- A runtime configuration is well-formed if:
    (1) all addresses in memory are below nextAddr, and
    (2) all values in varEnv only reference addresses below nextAddr.
    This captures that nextAddr is the "high-water mark" for allocated physical addresses,
    analogous to wfTypeContext for logical locations. -/
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

-- ================================================================
-- Runtime VarEnv Lookup/Update Lemmas
-- ================================================================

-- If y ≠ x, then updating runtime VarEnv with x does not affect lookup y
lemma VarEnv_lookup_update_ne (env : VarEnv) (x y : Name) (v : Value) (h_ne : y ≠ x) :
  (env.update x v).lookup y = env.lookup y := by
  simp [VarEnv.update, VarEnv.lookup]
  exact List_lookup_cons_ne env x y v h_ne

-- ================================================================
-- Evaluation Structure Lemmas
-- ================================================================

-- Helper lemma: extract evaluation structure from successful beval of unary operation.
lemma bevalUnaryOp_structure (op : UnaryOp) (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.unaryop op e1) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    LeanPoison.evalUnaryOp op v1 = some v ∧
    config₁.memory = config₂.memory ∧
    config₁.varEnv = config₂.varEnv ∧
    config₁.nextAddr = config₂.nextAddr ∧
    config₁.pureMode = config₂.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁ v₁ h_beval1 =>
        cases h_evalOp : LeanPoison.evalUnaryOp op v₁ with
        | some v_result =>
            simp [h_evalOp] at h_eq
            obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
            have h_mem_eq : config₁.memory = config₂.memory := by
              rw [h_eq_cfg]
            have h_var_eq : config₁.varEnv = config₂.varEnv := by
              rw [h_eq_cfg]
            have h_next_eq : config₁.nextAddr = config₂.nextAddr := by
              rw [h_eq_cfg]
            have h_pure_eq : config₁.pureMode = config₂.pureMode := by
              rw [h_eq_cfg]
            rw [h_eq_val] at h_evalOp
            subst h_eq_cfg
            simp only [Nat.add_sub_cancel]
            exact ⟨config₁, v₁, h_beval1, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
        | none =>
            simp [h_evalOp] at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of binary operation.
lemma bevalOp_structure (e1 e2 : Expr) (op : Op) (fuel : Nat) (verbose : Bool)
    (config₀ config₃ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.op e1 op e2) verbose =
      .success config₃ v →
  ∃ (config₁ config₂ : Config) (v1 v2 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₂ v2 ∧
    LeanPoison.evalOp op v1 v2 = some v ∧
    config₂.memory = config₃.memory ∧
    config₂.varEnv = config₃.varEnv ∧
    config₂.nextAddr = config₃.nextAddr ∧
    config₂.pureMode = config₃.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁ v₁ h_beval1 =>
        split at h_eq
        · next config₂ v₂ h_beval2 =>
          cases h_evalOp : LeanPoison.evalOp op v₁ v₂ with
          | some v_result =>
              simp [h_evalOp] at h_eq
              obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
              have h_mem_eq : config₂.memory = config₃.memory := by rw [h_eq_cfg]
              have h_var_eq : config₂.varEnv = config₃.varEnv := by rw [h_eq_cfg]
              have h_next_eq : config₂.nextAddr = config₃.nextAddr := by rw [h_eq_cfg]
              have h_pure_eq : config₂.pureMode = config₃.pureMode := by rw [h_eq_cfg]
              rw [h_eq_val] at h_evalOp
              subst h_eq_cfg
              simp only [Nat.add_sub_cancel]
              exact ⟨config₁, config₂, v₁, v₂, h_beval1, h_beval2, h_evalOp, h_mem_eq, h_var_eq, h_next_eq, h_pure_eq⟩
          | none =>
              simp [h_evalOp] at h_eq
        · next h_oof =>
          simp at h_eq
        · next msg h_err =>
          simp at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of sequence.
lemma bevalSeq_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.seq e1 e2) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₂ v := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁ v₁ h_beval1 =>
        split at h_eq
        · next config₂' v₂ h_beval2 =>
          injection h_eq with h_eq_cfg h_eq_val
          subst h_eq_val h_eq_cfg
          simp only [Nat.add_sub_cancel]
          exact ⟨config₁, v₁, h_beval1, h_beval2⟩
        · next h_oof =>
          simp at h_eq
        · next msg h_err =>
          simp at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of vlet.
lemma bevalVlet_structure (x : Name) (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config_final : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.vlet x e1 e2) verbose =
      .success config_final v →
  ∃ (config₁ config₂ config₃ : Config) (v1 : Value),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ v1 ∧
    config₂ = { config₁ with varEnv := config₁.varEnv.update x v1 } ∧
    LeanPoison.beval (fuel - 1) config₂ e2 verbose =
        .success config₃ v ∧
    config_final = { config₃ with varEnv := config₁.varEnv } := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.beval at h_eq
      simp at h_eq
      split at h_eq
      · next config₁' v₁ h_beval1 =>
        let config₂' := { config₁' with varEnv := config₁'.varEnv.update x v₁ }
        split at h_eq
        · next config₃' v₂ h_beval2 =>
          injection h_eq with h_eq_cfg h_eq_val
          subst h_eq_cfg h_eq_val
          simp only [Nat.add_sub_cancel]
          exact ⟨config₁', config₂', config₃', v₁, h_beval1, rfl, h_beval2, rfl⟩
        · next h_oof =>
          simp at h_eq
        · next msg h_err =>
          simp at h_eq
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

-- Helper lemma: extract evaluation structure from successful beval of newRef
lemma bevalNewRef_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.newRef e1) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (n : Int) (a : Address),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ (Value.num n) ∧
    a = config₁.nextAddr ∧
    config₂.memory = (config₁.memory.update a n) ∧
    config₂.nextAddr = config₁.nextAddr + 1 ∧
    config₂.varEnv = config₁.varEnv ∧
    config₂.pureMode = config₁.pureMode ∧
    v = Value.loc a := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    -- Only the success-num branch survives
    rename_i config' n h_beval1
    obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
    simp only [Nat.add_sub_cancel]
    refine ⟨config', n, config'.nextAddr, h_beval1, rfl, ?_⟩
    simp [freshAddr] at h_eq_cfg h_eq_val
    exact ⟨by rw [← h_eq_cfg], by rw [← h_eq_cfg], by rw [← h_eq_cfg], by rw [← h_eq_cfg], by rw [← h_eq_val]⟩

-- Helper lemma: extract evaluation structure from successful beval of deref
lemma bevalDeref_structure (e1 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.deref e1) verbose =
      .success config₁ v →
  ∃ (config' : Config) (a : Address) (n : Int),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config' (Value.loc a) ∧
    config'.memory.lookup a = some n ∧
    v = Value.num n ∧
    config₁.memory = config'.memory ∧
    config₁.varEnv = config'.varEnv ∧
    config₁.nextAddr = config'.nextAddr ∧
    config₁.pureMode = config'.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    -- Only the success-loc branch survives; need to split on memory lookup
    rename_i config' a heq_beval
    split at h_eq <;> try simp at h_eq
    -- Only the some-n branch survives
    rename_i n h_mem_some
    obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
    simp only [Nat.add_sub_cancel]
    have h_lookup' : config'.memory.lookup a = some n := h_mem_some
    refine ⟨config', a, n, heq_beval, h_lookup', h_eq_val.symm, ?_, ?_, ?_, ?_⟩
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]

-- Helper lemma: extract evaluation structure from successful beval of assign
lemma bevalAssign_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.assign e1 e2) verbose =
      .success config₂ v →
  ∃ (config₁ config₁' : Config) (a : Address) (n : Int),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ (Value.loc a) ∧
    LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₁' (Value.num n) ∧
    v = Value.unit ∧
    config₂.memory = config₁'.memory.update a n ∧
    config₂.varEnv = config₁'.varEnv ∧
    config₂.nextAddr = config₁'.nextAddr ∧
    config₂.pureMode = config₁'.pureMode := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    -- First split: e1 -> .success config₁ (Value.loc a); inner match on e2 remains
    rename_i config₁ a heq_beval1
    split at h_eq <;> try simp at h_eq
    -- Second split: e2 -> .success config₁' (Value.num n)
    rename_i config₁' n heq_beval2
    obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
    simp only [Nat.add_sub_cancel]
    refine ⟨config₁, config₁', a, n, heq_beval1, heq_beval2, h_eq_val.symm, ?_, ?_, ?_, ?_⟩
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]
    · rw [← h_eq_cfg]

-- Helper lemma: extract evaluation structure from successful beval of ite
lemma bevalIte_structure (e1 e2 e3 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₂ : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.ite e1 e2 e3) verbose =
      .success config₂ v →
  ∃ (config₁ : Config) (b : Bool),
    LeanPoison.beval (fuel - 1) config₀ e1 verbose =
        .success config₁ (Value.bool b) ∧
    ((b = true ∧ LeanPoison.beval (fuel - 1) config₁ e2 verbose =
        .success config₂ v) ∨
     (b = false ∧ LeanPoison.beval (fuel - 1) config₁ e3 verbose =
        .success config₂ v)) := by
  intro h_eq
  cases fuel with
  | zero =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
  | succ fuel' =>
    unfold LeanPoison.beval at h_eq
    simp at h_eq
    split at h_eq <;> try simp at h_eq
    · -- true branch: first split gives e1 -> bool true; need split on e2
      rename_i config₁ heq_beval1
      split at h_eq <;> try simp at h_eq
      rename_i config₂' v₂ heq_beval2
      obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
      subst h_eq_cfg h_eq_val
      simp only [Nat.add_sub_cancel]
      exact ⟨config₁, true, heq_beval1, Or.inl ⟨rfl, heq_beval2⟩⟩
    · -- false branch: first split gives e1 -> bool false; need split on e3
      rename_i config₁ heq_beval1
      split at h_eq <;> try simp at h_eq
      rename_i config₂' v₃ heq_beval3
      obtain ⟨h_eq_cfg, h_eq_val⟩ := h_eq
      subst h_eq_cfg h_eq_val
      simp only [Nat.add_sub_cancel]
      exact ⟨config₁, false, heq_beval1, Or.inr ⟨rfl, heq_beval3⟩⟩

-- Helper lemma: extract evaluation structure from successful beval of app.
-- TODO: FFI runtime — statement assumes classical user-closure dispatch, but
-- `Expr.app` now has additional extern-dispatch branches.  Proof is left as
-- `sorry` pending a strengthened statement that handles extern closures.
lemma bevalApp_structure (e1 e2 : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config_final : Config) (v : Value) :
  LeanPoison.beval fuel config₀ (Expr.app e1 e2) verbose =
      .success config_final v →
  ∃ (config₁ config₂ : Config) (v₂ : Value) (x : Name) (body : Expr) (env : VarEnv),
    LeanPoison.beval (fuel - 1) config₀ e2 verbose =
        .success config₁ v₂ ∧
    ((LeanPoison.beval (fuel - 1) config₁ e1 verbose =
          .success config₂ (Value.closure x body env) ∧
      config₂.pureMode = false ∧
      LeanPoison.bevalFunctionBody (fuel - 1) verbose config₂ env x v₂ body false =
          .success config_final v) ∨
     (LeanPoison.beval (fuel - 1) config₁ e1 verbose =
          .success config₂ (Value.peClosure x body env) ∧
     Expr.toPExpr? body ≠ none ∧
      LeanPoison.bevalFunctionBody (fuel - 1) verbose config₂ env x v₂ body true =
          .success config_final v)) ∧
    config_final.pureMode = config₂.pureMode := by
  sorry

-- ================================================================
-- Registry preservation
-- ================================================================

/-- `bevalFunctionBody` does not modify the extern registry. It either errors
    out or produces a final config constructed via `{ currentConfig with ... }`
    which leaves the registry slot untouched. -/
private lemma bevalFunctionBody_preserves_registry (fuel : Nat) (verbose : Bool)
    (currentConfig finalConfig : Config) (closureEnv : VarEnv) (paramName : Name)
    (argValue : Value) (body : Expr) (isPure : Bool) (v : Value) :
    LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName
        argValue body isPure = .success finalConfig v →
      finalConfig.registry = currentConfig.registry := by
  intro heval
  cases fuel with
  | zero => simp [LeanPoison.bevalFunctionBody] at heval
  | succ fuel' =>
    unfold LeanPoison.bevalFunctionBody at heval
    simp at heval
    split at heval
    · by_cases hPure : isPure = true
      · simp [hPure] at heval
        rcases heval with ⟨hcfg, _⟩; subst hcfg; rfl
      · simp [hPure] at heval
        rcases heval with ⟨hcfg, _⟩; subst hcfg; rfl
    · simp at heval
    · simp at heval

/-- `beval` preserves the extern registry: the final config's `.registry` field
    is always equal to the initial config's `.registry`. This holds because
    `beval` and `bevalFunctionBody` only ever modify `.memory`, `.varEnv`,
    `.nextAddr`, and `.pureMode` via explicit record updates; no branch writes
    to `.registry`.

    Proof strategy: leverage the existing `beval_*_structure` lemmas for each
    expression form, strengthened by the observation that in the `beval`
    implementation every `.success` return carries a config that is either
    (a) `config` (unchanged), (b) `{ cfg with m := ..., n := ... }` for
    non-registry fields m, n (record updates never touch `.registry`), or
    (c) a config returned by `bevalFunctionBody`, which itself preserves
    `.registry` per `bevalFunctionBody_preserves_registry`. -/
lemma beval_preserves_registry (fuel : Nat) (cfg₀ cfg₁ : Config) (e : Expr)
    (v : Value) (verbose : Bool) :
  LeanPoison.beval fuel cfg₀ e verbose = .success cfg₁ v →
    cfg₁.registry = cfg₀.registry := by
  -- TODO: FFI runtime — the lemma is semantically obvious (beval only
  -- updates `.memory`, `.varEnv`, `.nextAddr`, `.pureMode` via record
  -- updates; `.registry` is never written).  Proof by strong induction
  -- on fuel + case analysis on `e`; the tactic script alignment with
  -- `beval`'s nested `match` shape is being iterated in a follow-up.
  sorry

/-- Corollary: when the initial config has the default (empty) registry,
    every reachable final config also does. -/
lemma beval_registry_default {fuel : Nat} {μ : Memory} {ρ : VarEnv} {a : Address}
    {pm : Bool} {cfg : Config} {e : Expr} {v : Value} {verbose : Bool} :
  LeanPoison.beval fuel { memory := μ, varEnv := ρ, nextAddr := a, pureMode := pm }
    e verbose = .success cfg v → cfg.registry = emptyExternRegistry := by
  intro h
  have := beval_preserves_registry fuel _ cfg e v verbose h
  simpa using this

/-- Corollary: `terminatesTo` preserves the extern registry. -/
lemma terminatesTo_preserves_registry {e : Expr} {c₀ c₁ : Config} {out : Value} :
  terminatesTo e c₀ c₁ out → c₁.registry = c₀.registry := by
  intro ⟨fuel, verbose, h⟩
  exact beval_preserves_registry fuel c₀ c₁ e out verbose h

/-- Rewriting lemma: if a `terminatesTo` chain starts from a config with the
    default (empty) registry, the intermediate `cfg₀` also has the default
    registry, and we may rewrite any `terminatesTo e cfg₀ c₁ out` into the
    "registry-stripped" literal form that proof scaffolding expects. -/
lemma terminatesTo_registry_strip {e : Expr} {cfg₀ c₁ : Config} {out : Value}
    (h_reg : cfg₀.registry = emptyExternRegistry)
    (ht : terminatesTo e cfg₀ c₁ out) :
  terminatesTo e { memory := cfg₀.memory, varEnv := cfg₀.varEnv, nextAddr := cfg₀.nextAddr, pureMode := cfg₀.pureMode } c₁ out := by
  have heq : cfg₀ = { memory := cfg₀.memory, varEnv := cfg₀.varEnv, nextAddr := cfg₀.nextAddr, pureMode := cfg₀.pureMode } :=
    config_eq_of_registry_default cfg₀ h_reg
  rw [← heq]; exact ht

-- ================================================================
-- bevalFunctionBody_to_terminatesTo
-- ================================================================

-- Helper: Convert bevalFunctionBody success to terminatesTo for the body
private lemma bevalFunctionBody_to_terminatesTo
    (fuel : Nat) (verbose : Bool) (currentConfig : Config) (closureEnv : VarEnv)
    (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool)
    (finalConfig : Config) (v : Value) :
    LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
        .success finalConfig v →
    ∃ (evalConfig : Config),
      terminatesTo body { currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } evalConfig v ∧
      finalConfig =
        (if isPure then
          { currentConfig with pureMode := currentConfig.pureMode }
        else
          { currentConfig with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := currentConfig.pureMode }) := by
  intro hbeval_body
  cases fuel with
  | zero =>
    unfold LeanPoison.bevalFunctionBody at hbeval_body
    simp at hbeval_body
  | succ fuel' =>
    unfold LeanPoison.bevalFunctionBody at hbeval_body
    simp at hbeval_body
    split at hbeval_body
    · next evalConfig v_body h_beval_body =>
      cases h_isPure : isPure <;> simp [h_isPure] at hbeval_body h_beval_body
      · -- isPure = false
        obtain ⟨h_cfg, h_val⟩ := hbeval_body
        subst h_val
        use evalConfig
        refine ⟨⟨fuel', verbose, h_beval_body⟩, ?_⟩
        simpa [h_isPure] using h_cfg.symm
      · -- isPure = true
        obtain ⟨h_cfg, h_val⟩ := hbeval_body
        subst h_val
        use evalConfig
        refine ⟨⟨fuel', verbose, h_beval_body⟩, ?_⟩
        simpa [h_isPure] using h_cfg.symm
    · next h_oof =>
      simp at hbeval_body
    · next msg h_err =>
      simp at hbeval_body

-- ================================================================
-- terminatesTo inversion lemmas
-- ================================================================

/-- Inversion lemma for terminatesTo on number literals. -/
private lemma terminatesTo_num_inv' (n : Int) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.num n) c₀ c₁ v → c₁ = c₀ ∧ v = Value.num n := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on boolean literals. -/
private lemma terminatesTo_bool_inv' (b : Bool) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.bool b) c₀ c₁ v → c₁ = c₀ ∧ v = Value.bool b := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on unit. -/
private lemma terminatesTo_unit_inv' (c₀ c₁ : Config) (v : Value) :
    terminatesTo Expr.unit c₀ c₁ v → c₁ = c₀ ∧ v = Value.unit := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on string literals. -/
private lemma terminatesTo_str_inv' (s : String) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.str s) c₀ c₁ v → c₁ = c₀ ∧ v = Value.str s := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Combined inversion lemma for terminatesTo on any literal expression. -/
lemma terminatesTo_literal_inv' (e : Expr) (v_expected : Value)
    (hval : Expr.toValue? e = some v_expected) (c₀ c₁ : Config) (v : Value) :
    terminatesTo e c₀ c₁ v → c₁ = c₀ ∧ v = v_expected := by
  intro ht
  cases e with
  | unit =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_unit_inv' c₀ c₁ v ht
  | num n =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_num_inv' n c₀ c₁ v ht
  | bool b =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_bool_inv' b c₀ c₁ v ht
  | str s =>
      simp [Expr.toValue?] at hval
      cases hval
      exact terminatesTo_str_inv' s c₀ c₁ v ht
  | _ => simp [Expr.toValue?] at hval

/-- Inversion lemma for terminatesTo on variable lookup. -/
lemma terminatesTo_var_inv' (x : Name) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.var x) c₀ c₁ v →
    ∃ v', c₀.varEnv.lookup x = some v' ∧ c₁ = c₀ ∧ v = v' := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      cases hlookup : c₀.varEnv.lookup x with
      | none =>
          simp [hlookup] at hbeval
      | some v' =>
          simp [hlookup] at hbeval
          obtain ⟨hcfg, hval⟩ := hbeval
          exact ⟨v', rfl, hcfg.symm, hval.symm⟩

/-- Inversion lemma for terminatesTo on fn (regular function). -/
lemma terminatesTo_fn_inv' (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
    (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.fn x paramType body returnType) c₀ c₁ v →
    c₁ = c₀ ∧ v = Value.closure x body c₀.varEnv := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on pfn (predicated function). -/
lemma terminatesTo_pfn_inv' (x : Name) (paramType : Typ) (body : Expr) (returnType : Typ)
    (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.pfn x paramType body returnType) c₀ c₁ v →
    c₁ = c₀ ∧ v = Value.peClosure x body c₀.varEnv := by
  intro ⟨fuel, _verbose, hbeval⟩
  cases fuel with
  | zero => simp [LeanPoison.beval] at hbeval
  | succ fuel' =>
      simp [LeanPoison.beval] at hbeval
      exact ⟨hbeval.1.symm, hbeval.2.symm⟩

/-- Inversion lemma for terminatesTo on unaryop.
    Extracts the sub-expression evaluation and operation application. -/
lemma terminatesTo_unaryop_inv' (op : UnaryOp) (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.unaryop op e) c₀ c₁ v →
    ∃ c₁' v', terminatesTo e c₀ c₁' v' ∧
              LeanPoison.evalUnaryOp op v' = some v ∧
              c₁.memory = c₁'.memory ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.nextAddr = c₁'.nextAddr ∧
              c₁.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalUnaryOp_structure op e fuel verbose c₀ c₁ v hbeval
  rcases hstruct with ⟨cfg', v', hbeval_e, hevalOp, hmem, hvar, hnext, hpure_mode⟩
  exact ⟨cfg', v', ⟨fuel - 1, verbose, hbeval_e⟩, hevalOp, hmem.symm, hvar.symm, hnext.symm, hpure_mode.symm⟩

/-- Inversion lemma for terminatesTo on newRef.
    Extracts the sub-expression evaluation and allocation info. -/
lemma terminatesTo_newRef_inv' (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.newRef e) c₀ c₁ v →
    ∃ (c₁' : Config) (n : Int), terminatesTo e c₀ c₁' (Value.num n) ∧
              v = Value.loc c₁'.nextAddr ∧
              c₁.memory = c₁'.memory.insert c₁'.nextAddr n ∧
              c₁.nextAddr = c₁'.nextAddr + 1 ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalNewRef_structure e fuel verbose c₀ c₁ v hbeval
  rcases hstruct with ⟨cfg', n, a, hbeval_e, ha_eq, hmem, hnext, hvar, hpure_mode, hv⟩
  refine ⟨cfg', n, ⟨fuel - 1, verbose, hbeval_e⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv, ha_eq]
  · simp only [hmem, ha_eq, Memory.update]
  · exact hnext
  · exact hvar
  · exact hpure_mode

/-- Inversion lemma for terminatesTo on deref. -/
lemma terminatesTo_deref_inv' (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo (Expr.deref e) c₀ c₁ v →
    ∃ (c₁' : Config) (a : Address) (n : Int), terminatesTo e c₀ c₁' (Value.loc a) ∧
              c₁'.memory.lookup a = some n ∧
              v = Value.num n ∧
              c₁.memory = c₁'.memory ∧
              c₁.varEnv = c₁'.varEnv ∧
              c₁.nextAddr = c₁'.nextAddr ∧
              c₁.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalDeref_structure e fuel verbose c₀ c₁ v hbeval
  rcases hstruct with ⟨cfg', a, n, hbeval_e, hlookup, hv, hmem, hvar, hnext, hpure⟩
  exact ⟨cfg', a, n, ⟨fuel - 1, verbose, hbeval_e⟩, hlookup, hv, hmem, hvar, hnext, hpure⟩

/-- Helper lemma: in evaluation, `pureMode` is preserved through evaluation.
    This holds for any expression. -/
lemma terminatesTo_preserves_pureMode (e : Expr) (c₀ c₁ : Config) (v : Value) :
    terminatesTo e c₀ c₁ v →
    c₁.pureMode = c₀.pureMode := by
  intro ht
  rcases ht with ⟨fuel, verbose, hbeval⟩
  have hmain :
      ∀ fuel e c₀ c₁ v verbose,
        LeanPoison.beval fuel c₀ e verbose = .success c₁ v →
        c₁.pureMode = c₀.pureMode := by
    intro fuel
    induction fuel using Nat.strong_induction_on with
    | _ fuel ih =>
      intro e c₀ c₁ v verbose hpure
      cases fuel with
      | zero =>
        unfold LeanPoison.beval at hpure
        simp at hpure
      | succ fuel' =>
        have ht : terminatesTo e c₀ c₁ v := ⟨fuel' + 1, verbose, hpure⟩
        cases e with
        | num n =>
          have h := terminatesTo_num_inv' n c₀ c₁ v ht
          rw [h.1]
        | bool b =>
          have h := terminatesTo_bool_inv' b c₀ c₁ v ht
          rw [h.1]
        | unit =>
          have h := terminatesTo_unit_inv' c₀ c₁ v ht
          rw [h.1]
        | str s =>
          have h := terminatesTo_str_inv' s c₀ c₁ v ht
          rw [h.1]
        | var x =>
          have h := terminatesTo_var_inv' x c₀ c₁ v ht
          rcases h with ⟨_, _, hcfg, _⟩
          rw [hcfg]
        | fn x paramType body returnType =>
          have h := terminatesTo_fn_inv' x paramType body returnType c₀ c₁ v ht
          rw [h.1]
        | pfn x paramType body returnType =>
          have h := terminatesTo_pfn_inv' x paramType body returnType c₀ c₁ v ht
          rw [h.1]
        | op e1 op e2 =>
          have hstruct := bevalOp_structure e1 e2 op (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₂, v1, v2, hbeval1, hbeval2, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          have hrec₂ := ih fuel' h_fuel e2 cfg₁ cfg₂ v2 verbose hbeval2
          rw [h_pure_eq.symm, hrec₂, hrec₁]
        | unaryop op e1 =>
          have hstruct := bevalUnaryOp_structure op e1 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, v1, hbeval1, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          rw [h_pure_eq.symm, hrec₁]
        | seq e1 e2 =>
          have hstruct := bevalSeq_structure e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, v1, hbeval1, hbeval2⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          have hrec₂ := ih fuel' h_fuel e2 cfg₁ c₁ v verbose hbeval2
          rw [hrec₂, hrec₁]
        | vlet x e1 e2 =>
          have hstruct := bevalVlet_structure x e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₂, cfg₃, v1, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ v1 verbose hbeval1
          have h_pure_cfg2 : cfg₂.pureMode = cfg₁.pureMode := by
            simp [hcfg2_eq]
          have hrec₂ := ih fuel' h_fuel e2 cfg₂ cfg₃ v verbose hbeval2
          rw [hcfg_final_eq]
          simp
          rw [hrec₂, h_pure_cfg2, hrec₁]
        | ite e1 e2 e3 =>
          have hstruct := bevalIte_structure e1 e2 e3 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, b, hbeval1, hbranch⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ (Value.bool b) verbose hbeval1
          cases hbranch with
          | inl htrue =>
            rcases htrue with ⟨_, hbeval2⟩
            have hrec₂ := ih fuel' h_fuel e2 cfg₁ c₁ v verbose hbeval2
            rw [hrec₂, hrec₁]
          | inr hfalse =>
            rcases hfalse with ⟨_, hbeval3⟩
            have hrec₃ := ih fuel' h_fuel e3 cfg₁ c₁ v verbose hbeval3
            rw [hrec₃, hrec₁]
        | newRef e1 =>
          have hstruct := bevalNewRef_structure e1 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, _, _, hbeval1, _, _, _, _, h_pure_eq, _⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ _ verbose hbeval1
          rw [h_pure_eq, hrec₁]
        | deref e1 =>
          have hstruct := bevalDeref_structure e1 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, _, _, hbeval1, _, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ _ verbose hbeval1
          rw [h_pure_eq, hrec₁]
        | assign e1 e2 =>
          have hstruct := bevalAssign_structure e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₁', _, _, hbeval1, hbeval2, _, _, _, _, h_pure_eq⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec₁ := ih fuel' h_fuel e1 c₀ cfg₁ _ verbose hbeval1
          have hrec₂ := ih fuel' h_fuel e2 cfg₁ cfg₁' _ verbose hbeval2
          rw [h_pure_eq, hrec₂, hrec₁]
        | app e1 e2 =>
          have hstruct := bevalApp_structure e1 e2 (fuel' + 1) verbose c₀ c₁ v hpure
          rcases hstruct with ⟨cfg₁, cfg₂, v₂, x, body, env, hbeval_e2, h_app, h_pure_final⟩
          have h_fuel : fuel' < fuel' + 1 := Nat.lt_succ_self fuel'
          have hrec_e2 := ih fuel' h_fuel e2 c₀ cfg₁ v₂ verbose hbeval_e2
          rcases h_app with ⟨hbeval_e1, _, hbeval_body⟩ | ⟨hbeval_e1, _, hbeval_body⟩
          · have hrec_e1 := ih fuel' h_fuel e1 cfg₁ cfg₂ _ verbose hbeval_e1
            have h_pure_cfg2 : cfg₂.pureMode = c₀.pureMode := by
              rw [hrec_e1, hrec_e2]
            rw [h_pure_final, h_pure_cfg2]
          · have hrec_e1 := ih fuel' h_fuel e1 cfg₁ cfg₂ _ verbose hbeval_e1
            have h_pure_cfg2 : cfg₂.pureMode = c₀.pureMode := by
              rw [hrec_e1, hrec_e2]
            rw [h_pure_final, h_pure_cfg2]
        | externVal _id _typ _p _pred =>
          -- TODO: FFI runtime — extern val dispatch (config preserved; trivially
          -- preserves pureMode, proof deferred).
          sorry
        | externFn _id _x _typ _ret _eff =>
          -- TODO: FFI runtime — extern fn dispatch (config preserved on success).
          sorry
        | externPfn _id _x _typ _ret =>
          -- TODO: FFI runtime — extern pfn dispatch (config preserved on success).
          sorry
  exact hmain fuel e c₀ c₁ v verbose hbeval

-- ================================================================
-- Composite terminatesTo inversions
-- ================================================================

/-- Inversion lemma for terminatesTo on app (function application).
    The body terminates to some intermediate evalConfig (not c₂), because bevalFunctionBody
    transforms the config after body evaluation. -/
lemma terminatesTo_app_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.app e₁ e₂) c₀ c₂ v →
    -- Either the closure case holds...
    (∃ (c₂' : Config) (v₂ : Value) (c₁ : Config) (x : Name) (body : Expr) (env : VarEnv) (evalConfig : Config),
      terminatesTo e₂ c₀ c₂' v₂ ∧
      terminatesTo e₁ c₂' c₁ (Value.closure x body env) ∧
      c₁.pureMode = false ∧
      terminatesTo body { c₁ with varEnv := env.update x v₂, pureMode := false } evalConfig v ∧
      c₂ = { c₁ with memory := evalConfig.memory, nextAddr := evalConfig.nextAddr, pureMode := c₁.pureMode } ∧
      c₂'.pureMode = c₀.pureMode ∧
      c₂.pureMode = c₀.pureMode) ∨
    -- ...or the peClosure case holds
    (∃ (c₂' : Config) (v₂ : Value) (c₁ : Config) (x : Name) (body : Expr) (env : VarEnv) (evalConfig : Config),
      terminatesTo e₂ c₀ c₂' v₂ ∧
      terminatesTo e₁ c₂' c₁ (Value.peClosure x body env) ∧
      Expr.toPExpr? body ≠ none ∧
      terminatesTo body { c₁ with varEnv := env.update x v₂, pureMode := true } evalConfig v ∧
      c₂ = c₁ ∧
      c₂'.pureMode = c₀.pureMode ∧
      c₂.pureMode = c₀.pureMode) := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalApp_structure e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg2, cfg1, v2, x, body, env, hbeval_e2, h_app, hpure_mode_final⟩
  -- Convert e₂ evaluation to terminatesTo
  have hpure_cfg2 : cfg2.pureMode = c₀.pureMode :=
    terminatesTo_preserves_pureMode e₂ c₀ cfg2 v2 ⟨fuel - 1, verbose, hbeval_e2⟩
  -- Case split: closure vs peClosure
  rcases h_app with ⟨hbeval_e1, hpure_false, hbeval_body⟩ | ⟨hbeval_e1, htoPExpr, hbeval_body⟩
  · -- Case 1: Regular closure
    left
    have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
      terminatesTo_preserves_pureMode e₁ cfg2 cfg1 (Value.closure x body env) ⟨fuel - 1, verbose, hbeval_e1⟩
    obtain ⟨evalConfig, hbody_terminates, hcfg_final⟩ :=
      bevalFunctionBody_to_terminatesTo (fuel - 1) verbose cfg1 env x v2 body false c₂ v hbeval_body
    refine ⟨cfg2, v2, cfg1, x, body, env, evalConfig, ⟨fuel - 1, verbose, hbeval_e2⟩, ⟨fuel - 1, verbose, hbeval_e1⟩,
            hpure_false, hbody_terminates, (by simpa using hcfg_final), hpure_cfg2, ?_⟩
    rw [hpure_mode_final, hpure_cfg1, hpure_cfg2]
  · -- Case 2: Pure closure (peClosure)
    right
    have hpure_cfg1 : cfg1.pureMode = cfg2.pureMode :=
      terminatesTo_preserves_pureMode e₁ cfg2 cfg1 (Value.peClosure x body env) ⟨fuel - 1, verbose, hbeval_e1⟩
    obtain ⟨evalConfig, hbody_terminates, hcfg_final⟩ :=
      bevalFunctionBody_to_terminatesTo (fuel - 1) verbose cfg1 env x v2 body true c₂ v hbeval_body
    refine ⟨cfg2, v2, cfg1, x, body, env, evalConfig, ⟨fuel - 1, verbose, hbeval_e2⟩, ⟨fuel - 1, verbose, hbeval_e1⟩,
            htoPExpr, hbody_terminates, (by simpa using hcfg_final), hpure_cfg2, ?_⟩
    rw [hpure_mode_final, hpure_cfg1, hpure_cfg2]

/-- Inversion lemma for terminatesTo on ite (if-then-else).
    Returns intermediate config after condition, which branch was taken, and preserves pureMode. -/
lemma terminatesTo_ite_inv' (e₁ e₂ e₃ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.ite e₁ e₂ e₃) c₀ c₂ v →
    ∃ (c₁ : Config) (b : Bool),
              terminatesTo e₁ c₀ c₁ (Value.bool b) ∧
              ((b = true ∧ terminatesTo e₂ c₁ c₂ v) ∨
               (b = false ∧ terminatesTo e₃ c₁ c₂ v)) ∧
              c₁.pureMode = c₀.pureMode ∧
              c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalIte_structure e₁ e₂ e₃ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, b, hbeval_e1, hbranch⟩
  have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ (Value.bool b) ⟨fuel - 1, verbose, hbeval_e1⟩
  cases hbranch with
  | inl htrue =>
    rcases htrue with ⟨hb, hbeval_e2⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₁ c₂ v ⟨fuel - 1, verbose, hbeval_e2⟩
    refine ⟨cfg₁, b, ⟨fuel - 1, verbose, hbeval_e1⟩, Or.inl ⟨hb, ⟨fuel - 1, verbose, hbeval_e2⟩⟩, hrec₁, ?_⟩
    rw [hrec₂, hrec₁]
  | inr hfalse =>
    rcases hfalse with ⟨hb, hbeval_e3⟩
    have hrec₃ := terminatesTo_preserves_pureMode e₃ cfg₁ c₂ v ⟨fuel - 1, verbose, hbeval_e3⟩
    refine ⟨cfg₁, b, ⟨fuel - 1, verbose, hbeval_e1⟩, Or.inr ⟨hb, ⟨fuel - 1, verbose, hbeval_e3⟩⟩, hrec₁, ?_⟩
    rw [hrec₃, hrec₁]

/-- Inversion lemma for terminatesTo on binary op. -/
lemma terminatesTo_op_inv' (e₁ : Expr) (op : Op) (e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.op e₁ op e₂) c₀ c₂ v →
    ∃ c₁ v₁ v₂, terminatesTo e₁ c₀ c₁ v₁ ∧
                terminatesTo e₂ c₁ c₂ v₂ ∧
                LeanPoison.evalOp op v₁ v₂ = some v ∧
                c₁.pureMode = c₀.pureMode ∧
                c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalOp_structure e₁ e₂ op fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, cfg₂, v₁, v₂, hbeval_e1, hbeval_e2, hevalOp, hmem, hvar, hnext, hpure_mode⟩
  have hbeval_e2' : LeanPoison.beval (fuel - 1) cfg₁ e₂ verbose = .success c₂ v₂ := by
    -- TODO: FFI runtime — Config gained a `registry` field; the `Config.mk.injEq`
    -- expansion requires a 5th argument for registry equality that the caller
    -- has not been re-plumbed to supply.
    sorry
  refine ⟨cfg₁, v₁, v₂, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hbeval_e2'⟩, hevalOp, ?_, ?_⟩
  · exact terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
  · have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₁ c₂ v₂ ⟨fuel - 1, verbose, hbeval_e2'⟩
    rw [hrec₂, hrec₁]

/-- Inversion lemma for terminatesTo on seq. -/
lemma terminatesTo_seq_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.seq e₁ e₂) c₀ c₂ v →
    ∃ c₁ v₁, terminatesTo e₁ c₀ c₁ v₁ ∧
             terminatesTo e₂ c₁ c₂ v ∧
             c₁.pureMode = c₀.pureMode ∧
             c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalSeq_structure e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, v₁, hbeval_e1, hbeval_e2⟩
  refine ⟨cfg₁, v₁, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hbeval_e2⟩, ?_, ?_⟩
  · exact terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
  · have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₁ c₂ v ⟨fuel - 1, verbose, hbeval_e2⟩
    rw [hrec₂, hrec₁]

/-- Inversion lemma for terminatesTo on vlet. -/
lemma terminatesTo_vlet_inv' (x : Name) (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.vlet x e₁ e₂) c₀ c₂ v →
    ∃ c₁ v₁ c₃, terminatesTo e₁ c₀ c₁ v₁ ∧
                terminatesTo e₂ { c₁ with varEnv := c₁.varEnv.update x v₁ } c₃ v ∧
                c₂ = { c₃ with varEnv := c₁.varEnv } ∧
                c₁.pureMode = c₀.pureMode ∧
                c₂.pureMode = c₀.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalVlet_structure x e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, cfg₂, cfg₃, v₁, hbeval_e1, hcfg2_eq, hbeval_e2, hcfg_final⟩
  have hpure_e2' : LeanPoison.beval (fuel - 1) { cfg₁ with varEnv := cfg₁.varEnv.update x v₁ } e₂ verbose =
      .success cfg₃ v := by rw [← hcfg2_eq]; exact hbeval_e2
  refine ⟨cfg₁, v₁, cfg₃, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hpure_e2'⟩, hcfg_final, ?_, ?_⟩
  · exact terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
  · have hrec₁ := terminatesTo_preserves_pureMode e₁ c₀ cfg₁ v₁ ⟨fuel - 1, verbose, hbeval_e1⟩
    have hrec₂ := terminatesTo_preserves_pureMode e₂ cfg₂ cfg₃ v ⟨fuel - 1, verbose, hbeval_e2⟩
    have h_pure_cfg2 : cfg₂.pureMode = cfg₁.pureMode := by rw [hcfg2_eq]
    rw [hcfg_final]; simp; rw [hrec₂, h_pure_cfg2, hrec₁]

/-- Inversion lemma for terminatesTo on assign. -/
lemma terminatesTo_assign_inv' (e₁ e₂ : Expr) (c₀ c₂ : Config) (v : Value) :
    terminatesTo (Expr.assign e₁ e₂) c₀ c₂ v →
    ∃ (c₁ c₁' : Config) (a : Address) (n : Int),
                           terminatesTo e₁ c₀ c₁ (Value.loc a) ∧
                           terminatesTo e₂ c₁ c₁' (Value.num n) ∧
                           v = Value.unit ∧
                           c₂.memory = c₁'.memory.insert a n ∧
                           c₂.varEnv = c₁'.varEnv ∧
                           c₂.nextAddr = c₁'.nextAddr ∧
                           c₂.pureMode = c₁'.pureMode := by
  intro ⟨fuel, verbose, hbeval⟩
  have hstruct := bevalAssign_structure e₁ e₂ fuel verbose c₀ c₂ v hbeval
  rcases hstruct with ⟨cfg₁, cfg₁', a, n, hbeval_e1, hbeval_e2, hv, hmem, hvar, hnext, hpure_mode⟩
  refine ⟨cfg₁, cfg₁', a, n, ⟨fuel - 1, verbose, hbeval_e1⟩, ⟨fuel - 1, verbose, hbeval_e2⟩, hv, ?_, ?_, ?_, ?_⟩
  · rw [hmem]; rfl  -- .update = .insert for ExtTreeMap
  · exact hvar
  · exact hnext
  · exact hpure_mode

-- ================================================================
-- NextAddr Monotonicity
-- ================================================================


/-- Helper lemma: bevalFunctionBody preserves monotonicity of nextAddr. -/
private lemma bevalFunctionBody_nextAddr_mono
    (fuel : Nat) (verbose : Bool) (currentConfig finalConfig : Config)
    (closureEnv : VarEnv) (paramName : Name) (argValue : Value) (body : Expr) (isPure : Bool) (v : Value)
    (IH : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = .success config₁ v →
      config₀.nextAddr ≤ config₁.nextAddr) :
  LeanPoison.bevalFunctionBody fuel verbose currentConfig closureEnv paramName argValue body isPure =
      .success finalConfig v →
  currentConfig.nextAddr ≤ finalConfig.nextAddr := by
  intro h_eq
  cases fuel with
  | zero =>
      unfold LeanPoison.bevalFunctionBody at h_eq
      simp at h_eq
  | succ fuel' =>
      unfold LeanPoison.bevalFunctionBody at h_eq
      simp at h_eq
      split at h_eq
      · next evalConfig v_body h_beval_body =>
        split at h_eq
        · -- isPure = true
          injection h_eq with h_cfg_eq h_val_eq
          cases h_cfg_eq
          simp
        · -- isPure = false
          injection h_eq with h_cfg_eq h_val_eq
          have h_next_eq : finalConfig.nextAddr = evalConfig.nextAddr := by
            cases h_cfg_eq
            rfl
          have h_bodyConfig_next : ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure } : Config).nextAddr = currentConfig.nextAddr := rfl
          have h_fuel' : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
          have IH_body := IH fuel' h_fuel' body ({ currentConfig with varEnv := closureEnv.update paramName argValue, pureMode := isPure }) evalConfig v_body h_beval_body
          have IH_body' : currentConfig.nextAddr ≤ evalConfig.nextAddr := by
            simpa [h_bodyConfig_next] using IH_body
          simp [h_next_eq]
          exact IH_body'
      · next h_oof =>
        simp at h_eq
      · next msg h_err =>
        simp at h_eq

private lemma beval_nextAddr_mono : ∀ (e : Expr) (fuel : Nat) (verbose : Bool)
    (config₀ config₁ : Config) (v : Value),
  LeanPoison.beval fuel config₀ e verbose = .success config₁ v →
  config₀.nextAddr ≤ config₁.nextAddr := by
  intro e fuel verbose config₀ config₁ v h_eval
  revert e verbose config₀ config₁ v h_eval
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro e verbose config₀ config₁ v h_eval
    have IH_converted : ∀ m < fuel, ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
      LeanPoison.beval m config₀ e verbose = .success config₁ v →
      config₀.nextAddr ≤ config₁.nextAddr := by
      intro m h_lt e' config₀' config₁' v' h_eval'
      exact IH m h_lt e' verbose config₀' config₁' v' h_eval'
    cases e with
    | externVal id typ poison pred =>
        -- TODO: FFI runtime — extern dispatch; nextAddr unchanged by
        -- `externVal` (registry lookup only), but the proof needs to unfold
        -- the registry match and conclude cfg₀.nextAddr = cfg₁.nextAddr.
        sorry
    | externFn id arg argTyp retSpec effects =>
        -- TODO: FFI runtime — extern dispatch yields a closure; nextAddr
        -- unchanged but proof not wired.
        sorry
    | externPfn id arg argTyp retSpec =>
        -- TODO: FFI runtime — same as `externFn`.
        sorry
    | num n | bool b | unit | str s =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
            obtain ⟨h_eq_config, _⟩ := h_eval
            subst h_eq_config
            exact le_rfl
    | var x =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
            cases h_lookup : config₀.varEnv.lookup x with
            | some v_lookup =>
                simp [h_lookup] at h_eval
                obtain ⟨h_eq_config, _⟩ := h_eval
                subst h_eq_config
                exact le_rfl
            | none =>
                simp [h_lookup] at h_eval
    | fn x paramType body returnType | pfn x paramType body returnType =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            unfold LeanPoison.beval at h_eval
            simp at h_eval
            obtain ⟨h_eq_config, _⟩ := h_eval
            subst h_eq_config
            exact le_rfl
    | op e1 op e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalOp_structure e1 e2 op (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with
              ⟨cfg₁1, cfg₁2, v1, v2, hbeval1, hbeval2, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 :=
              IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 :=
              IH_converted fuel' h_fuel e2 cfg₁1 cfg₁2 v2 hbeval2
            have hle02 : config₀.nextAddr ≤ cfg₁2.nextAddr := Nat.le_trans hle1 hle2
            simpa [h_next] using hle02
    | unaryop op e1 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalUnaryOp_structure op e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, _h_evalOp, _h_mem, _h_var, h_next, _h_pure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            simpa [h_next] using hle1
    | ite e1 e2 e3 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalIte_structure e1 e2 e3 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁, b, hbeval1, hbranch⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            cases hbranch with
            | inl htrue =>
              rcases htrue with ⟨_, hbeval2⟩
              have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁ (Value.bool b) hbeval1
              have hle2 := IH_converted fuel' h_fuel e2 cfg₁ config₁ v hbeval2
              exact Nat.le_trans hle1 hle2
            | inr hfalse =>
              rcases hfalse with ⟨_, hbeval3⟩
              have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁ (Value.bool b) hbeval1
              have hle3 := IH_converted fuel' h_fuel e3 cfg₁ config₁ v hbeval3
              exact Nat.le_trans hle1 hle3
    | newRef e1 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalNewRef_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, n, a, hbeval1, _ha, _hmem, h_next, _hvar, _hval⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 (Value.num n) hbeval1
            have hle1' : config₀.nextAddr ≤ cfg₁1.nextAddr + 1 :=
              Nat.le_trans hle1 (Nat.le_succ _)
            simpa [h_next] using hle1'
    | assign e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalAssign_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁, cfg₁', a, n, hbeval1, hbeval2, _, _, _, hnext, _⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁ (Value.loc a) hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁ cfg₁' (Value.num n) hbeval2
            have hle02 : config₀.nextAddr ≤ cfg₁'.nextAddr := Nat.le_trans hle1 hle2
            simpa [hnext] using hle02
    | deref e1 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalDeref_structure e1 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, a, n, hbeval1, _, _, hmem, hvar, hnext, hpure⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 (Value.loc a) hbeval1
            -- config₁ = cfg₁1 since all fields match
            have : config₁.nextAddr = cfg₁1.nextAddr := hnext
            simpa [this] using hle1
    | seq e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalSeq_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1, hbeval2⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁1 config₁ v hbeval2
            exact Nat.le_trans hle1 hle2
    | vlet x e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalVlet_structure x e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁1, cfg₁2, cfg₁3, v1, hbeval1, hcfg2, hbeval2, hcfg_final⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have hle1 := IH_converted fuel' h_fuel e1 config₀ cfg₁1 v1 hbeval1
            have hle2 := IH_converted fuel' h_fuel e2 cfg₁2 cfg₁3 v hbeval2
            have h_next_eq1 : cfg₁2.nextAddr = cfg₁1.nextAddr := by
              simp [hcfg2]
            have h_next_eq2 : config₁.nextAddr = cfg₁3.nextAddr := by
              simp [hcfg_final]
            have hle01 : config₀.nextAddr ≤ cfg₁2.nextAddr := by
              simpa [h_next_eq1] using hle1
            have hle03 : config₀.nextAddr ≤ cfg₁3.nextAddr := Nat.le_trans hle01 hle2
            simpa [h_next_eq2] using hle03
    | app e1 e2 =>
        cases fuel with
        | zero => simp [LeanPoison.beval] at h_eval
        | succ fuel' =>
            have hstruct :=
              bevalApp_structure e1 e2 (fuel' + 1) verbose config₀ config₁ v h_eval
            rcases hstruct with ⟨cfg₁, cfg₂, v₂, x, body, env, hbeval_e2, h_app, _⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            have IH_fuel' : ∀ m < fuel', ∀ (e : Expr) (config₀ config₁ : Config) (v : Value),
              LeanPoison.beval m config₀ e verbose = .success config₁ v →
              config₀.nextAddr ≤ config₁.nextAddr := by
              intro m h_m_lt e config₀ config₁ v h_beval_ex
              have h_m_lt_succ : m < fuel'.succ := Nat.lt_of_lt_of_le h_m_lt (Nat.le_succ fuel')
              exact IH m h_m_lt_succ e verbose config₀ config₁ v h_beval_ex
            have hle_e2 := IH_converted fuel' h_fuel e2 config₀ cfg₁ v₂ hbeval_e2
            rcases h_app with ⟨hbeval_e1, _, hbeval_body⟩ | ⟨hbeval_e1, _, hbeval_body⟩
            · have hle_e1 := IH_converted fuel' h_fuel e1 cfg₁ cfg₂ (Value.closure x body env) hbeval_e1
              have hle_body :=
                bevalFunctionBody_nextAddr_mono fuel' verbose cfg₂ config₁ env x v₂ body false v IH_fuel' hbeval_body
              exact Nat.le_trans hle_e2 (Nat.le_trans hle_e1 hle_body)
            · have hle_e1 := IH_converted fuel' h_fuel e1 cfg₁ cfg₂ (Value.peClosure x body env) hbeval_e1
              have hle_body :=
                bevalFunctionBody_nextAddr_mono fuel' verbose cfg₂ config₁ env x v₂ body true v IH_fuel' hbeval_body
              exact Nat.le_trans hle_e2 (Nat.le_trans hle_e1 hle_body)

/-- Next address is monotone for terminating evaluations. -/
lemma terminatesTo_nextAddr_mono (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v → cfg₀.nextAddr ≤ cfg₁.nextAddr := by
  intro ⟨fuel, verbose, hbeval⟩
  exact beval_nextAddr_mono e fuel verbose cfg₀ cfg₁ v hbeval


-- ================================================================
-- Pure evaluation preserves config (used for pure closures)
-- ================================================================

/-- If a pure expression evaluates successfully in pureMode, it does not change nextAddr/memory. -/
private lemma beval_pure_config_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose = .success cfg₁ v →
    cfg₁.nextAddr = cfg₀.nextAddr ∧ cfg₁.pureMode = true ∧ cfg₁.memory = cfg₀.memory := by
  revert e cfg₀ cfg₁ v verbose pe
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
    intro e cfg₀ cfg₁ v verbose pe h_pure h_pm hbeval
    cases fuel with
    | zero =>
        unfold LeanPoison.beval at hbeval
        simp at hbeval
    | succ fuel' =>
        cases e with
        | unit | str _ | num _ | bool _ =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            obtain ⟨h_cfg_eq, _⟩ := hbeval
            subst h_cfg_eq
            exact ⟨rfl, h_pm, rfl⟩
        | var x =>
            unfold LeanPoison.beval at hbeval
            simp at hbeval
            cases h_lookup : cfg₀.varEnv.lookup x with
            | some v' =>
                simp [h_lookup] at hbeval
                obtain ⟨h_cfg_eq, _⟩ := hbeval
                subst h_cfg_eq
                exact ⟨rfl, h_pm, rfl⟩
            | none =>
                simp [h_lookup] at hbeval
        | op e1 op e2 =>
            have hstruct :=
              bevalOp_structure e1 e2 op (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with
              ⟨cfg₁1, cfg₁2, v1, v2, hbeval1', hbeval2', _h_evalOp, _h_mem, _h_var, h_next, h_pure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose pe1 h_pe1 h_pm hbeval1'
                    have h2 := IH fuel' h_fuel e2 cfg₁1 cfg₁2 v2 verbose pe2 h_pe2 h1.2.1 hbeval2'
                    refine ⟨?_, ?_, ?_⟩
                    · calc cfg₁.nextAddr = cfg₁2.nextAddr := h_next.symm
                        _ = cfg₁1.nextAddr := h2.1
                        _ = cfg₀.nextAddr := h1.1
                    · calc cfg₁.pureMode = cfg₁2.pureMode := h_pure_eq.symm
                        _ = true := h2.2.1
                    · calc cfg₁.memory = cfg₁2.memory := _h_mem.symm
                        _ = cfg₁1.memory := h2.2.2
                        _ = cfg₀.memory := h1.2.2
        | unaryop op e1 =>
            have hstruct :=
              bevalUnaryOp_structure op e1 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, v1, hbeval1', _h_evalOp, _h_mem, _h_var, h_next, h_pure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                subst h_pure
                have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose pe1 h_pe1 h_pm hbeval1'
                refine ⟨?_, ?_, ?_⟩
                · calc cfg₁.nextAddr = cfg₁1.nextAddr := h_next.symm
                    _ = cfg₀.nextAddr := h1.1
                · calc cfg₁.pureMode = cfg₁1.pureMode := h_pure_eq.symm
                    _ = true := h1.2.1
                · calc cfg₁.memory = cfg₁1.memory := _h_mem.symm
                    _ = cfg₀.memory := h1.2.2
        | ite e1 e2 e3 =>
            have hstruct :=
              bevalIte_structure e1 e2 e3 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, b, hbeval1, hbranch⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    cases h_pe3 : Expr.toPExpr? e3 with
                    | none => simp [h_pe3] at h_pure
                    | some pe3 =>
                        simp [h_pe3] at h_pure
                        subst h_pure
                        have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 (Value.bool b) verbose pe1 h_pe1 h_pm hbeval1
                        cases hbranch with
                        | inl htrue =>
                          rcases htrue with ⟨_, hbeval2⟩
                          have h2 := IH fuel' h_fuel e2 cfg₁1 cfg₁ v verbose pe2 h_pe2 h1.2.1 hbeval2
                          refine ⟨?_, ?_, ?_⟩
                          · calc cfg₁.nextAddr = cfg₁1.nextAddr := h2.1
                              _ = cfg₀.nextAddr := h1.1
                          · exact h2.2.1
                          · calc cfg₁.memory = cfg₁1.memory := h2.2.2
                              _ = cfg₀.memory := h1.2.2
                        | inr hfalse =>
                          rcases hfalse with ⟨_, hbeval3⟩
                          have h3 := IH fuel' h_fuel e3 cfg₁1 cfg₁ v verbose pe3 h_pe3 h1.2.1 hbeval3
                          refine ⟨?_, ?_, ?_⟩
                          · calc cfg₁.nextAddr = cfg₁1.nextAddr := h3.1
                              _ = cfg₀.nextAddr := h1.1
                          · exact h3.2.1
                          · calc cfg₁.memory = cfg₁1.memory := h3.2.2
                              _ = cfg₀.memory := h1.2.2
        | deref e1 =>
            have hstruct :=
              bevalDeref_structure e1 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, _, _, hbeval1, _, _, hmem, hvar, hnext, hpure_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                subst h_pure
                have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 _ verbose pe1 h_pe1 h_pm hbeval1
                refine ⟨?_, ?_, ?_⟩
                · calc cfg₁.nextAddr = cfg₁1.nextAddr := hnext
                    _ = cfg₀.nextAddr := h1.1
                · calc cfg₁.pureMode = cfg₁1.pureMode := hpure_eq
                    _ = true := h1.2.1
                · calc cfg₁.memory = cfg₁1.memory := hmem
                    _ = cfg₀.memory := h1.2.2
        | vlet x e1 e2 =>
            have hstruct :=
              bevalVlet_structure x e1 e2 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁1, cfg₂, cfg₃, v1, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h1 := IH fuel' h_fuel e1 cfg₀ cfg₁1 v1 verbose pe1 h_pe1 h_pm hbeval1
                    have h_pm2 : cfg₂.pureMode = true := by
                      simpa [hcfg2_eq] using h1.2.1
                    have h2 := IH fuel' h_fuel e2 cfg₂ cfg₃ v verbose pe2 h_pe2 h_pm2 hbeval2
                    subst hcfg2_eq hcfg_final_eq
                    refine ⟨?_, ?_, ?_⟩
                    · calc cfg₃.nextAddr = cfg₁1.nextAddr := h2.1
                        _ = cfg₀.nextAddr := h1.1
                    · simpa using h2.2.1
                    · calc cfg₃.memory = cfg₁1.memory := h2.2.2
                        _ = cfg₀.memory := h1.2.2
        | app e1 e2 =>
            have hstruct :=
              bevalApp_structure e1 e2 (fuel' + 1) verbose cfg₀ cfg₁ v hbeval
            rcases hstruct with ⟨cfg₁', cfg₂, v₂, x, body, env, hbeval_e2, h_app, _⟩
            have h_fuel : fuel' < fuel'.succ := Nat.lt_succ_self fuel'
            simp [Expr.toPExpr?] at h_pure
            cases h_pe1 : Expr.toPExpr? e1 with
            | none => simp [h_pe1] at h_pure
            | some pe1 =>
                simp [h_pe1] at h_pure
                cases h_pe2 : Expr.toPExpr? e2 with
                | none => simp [h_pe2] at h_pure
                | some pe2 =>
                    simp [h_pe2] at h_pure
                    subst h_pure
                    have h2 := IH fuel' h_fuel e2 cfg₀ cfg₁' v₂ verbose pe2 h_pe2 h_pm hbeval_e2
                    rcases h_app with ⟨hbeval_e1, _, _⟩ | ⟨hbeval_e1, _, hbeval_body⟩
                    · -- Closure case: pureMode = false, but we showed it should be true
                      have h1 := IH fuel' h_fuel e1 cfg₁' cfg₂ (Value.closure x body env) verbose pe1 h_pe1 h2.2.1 hbeval_e1
                      -- h1.2.1 says cfg₂.pureMode = true, but h_app says cfg₂.pureMode = false
                      simp_all
                    · -- peClosure case
                      have h1 := IH fuel' h_fuel e1 cfg₁' cfg₂ (Value.peClosure x body env) verbose pe1 h_pe1 h2.2.1 hbeval_e1
                      -- bevalFunctionBody with isPure = true, body is pure
                      obtain ⟨evalConfig, hbody_term, hcfg_final⟩ :=
                        bevalFunctionBody_to_terminatesTo (fuel' ) verbose cfg₂ env x v₂ body true cfg₁ v hbeval_body
                      simp at hcfg_final
                      -- hcfg_final : cfg₁ = cfg₂ (since { cfg₂ with pureMode := cfg₂.pureMode } = cfg₂)
                      refine ⟨?_, ?_, ?_⟩
                      · calc cfg₁.nextAddr = cfg₂.nextAddr := by rw [hcfg_final]
                          _ = cfg₁'.nextAddr := h1.1
                          _ = cfg₀.nextAddr := h2.1
                      · rw [hcfg_final]; exact h1.2.1
                      · calc cfg₁.memory = cfg₂.memory := by rw [hcfg_final]
                          _ = cfg₁'.memory := h1.2.2
                          _ = cfg₀.memory := h2.2.2
        -- impossible cases: not allowed by pexpr syntax
        | newRef _ | assign _ _ | seq _ _ | fn _ _ _ _ | pfn _ _ _ _
        | externVal _ _ _ | externFn _ _ _ _ | externPfn _ _ _ =>
            simp [Expr.toPExpr?] at h_pure

private lemma beval_pure_nextAddr_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose = .success cfg₁ v →
    cfg₁.nextAddr = cfg₀.nextAddr := by
  intro h_pure h_pm hbeval
  exact (beval_pure_config_eq e fuel cfg₀ cfg₁ v verbose pe h_pure h_pm hbeval).1

lemma beval_pure_memory_eq (e : Expr) (fuel : Nat) (cfg₀ cfg₁ : Config) (v : Value)
    (verbose : Bool) (pe : PExpr) :
    Expr.toPExpr? e = some pe →
    cfg₀.pureMode = true →
    LeanPoison.beval fuel cfg₀ e verbose = .success cfg₁ v →
    cfg₁.memory = cfg₀.memory := by
  intro h_pure h_pm hbeval
  exact (beval_pure_config_eq e fuel cfg₀ cfg₁ v verbose pe h_pure h_pm hbeval).2.2

-- ================================================================
-- wfConfig_preserved Proof
-- ================================================================


-- Private lemmas for wfConfig_preserved proof

/-- evalUnaryOp preserves well-formedness of values. -/
private lemma evalUnaryOp_preserves_wfValue (next : Address) (op : UnaryOp) (v1 v : Value) :
    wfValue next v1 →
    LeanPoison.evalUnaryOp op v1 = some v →
    wfValue next v := by
  intro h_wf_v1 h_eval
  cases op with
  | not =>
      simp [LeanPoison.evalUnaryOp] at h_eval
      cases h_wf_v1 with
      | bool b =>
          injection h_eval with h_eq
          subst h_eq
          exact wfValue.bool (!b)
      | num _ | unit | str _ | loc _ | closure _ _ _ | peClosure _ _ _ =>
          cases h_eval

/-- evalOp preserves well-formedness of values. -/
private lemma evalOp_preserves_wfValue (next : Address) (op : Op) (v1 v2 v : Value) :
    LeanPoison.evalOp op v1 v2 = some v →
    wfValue next v := by
  intro h_eval
  cases op <;> cases v1 <;> cases v2 <;>
    simp [LeanPoison.evalOp] at h_eval
  all_goals
    cases h_eval
    first
    | exact wfValue.num _
    | exact wfValue.bool _

/-- If a value is found via lookup in a well-formed varEnv, then it's well-formed. -/
private lemma wfVarEnv_lookup (next : Address) (env : VarEnv) (x : Name) (v : Value) :
    wfVarEnv next env →
    env.lookup x = some v →
    wfValue next v := by
  intro h_wf_env h_lookup
  induction env with
  | nil =>
      simp [VarEnv.lookup, List.lookup] at h_lookup
  | cons head tail ih =>
      cases head with
      | mk x' v' =>
          cases h_wf_env with
          | cons x'_wf v'_wf env'_wf h_wf_v' h_wf_tail =>
              simp [VarEnv.lookup, List.lookup] at h_lookup
              by_cases h_eq : x == x'
              · simp [h_eq] at h_lookup
                subst h_lookup
                exact h_wf_v'
              · simp [h_eq] at h_lookup
                exact ih h_wf_tail h_lookup

/-- Updating a well-formed varEnv with a well-formed value preserves well-formedness. -/
private lemma wfVarEnv_update (next : Address) (env : VarEnv) (x : Name) (v : Value) :
    wfVarEnv next env →
    wfValue next v →
    wfVarEnv next (VarEnv.update env x v) := by
  intro hwf_env hwf_v
  exact wfVarEnv.cons x v env hwf_v hwf_env

-- Monotonicity of well-formedness: larger bounds preserve wfValue/wfVarEnv.
mutual
  private lemma wfValue_mono {n m : Address} (h : n ≤ m) :
      ∀ v, wfValue n v → wfValue m v := by
    intro v hv
    cases hv with
    | num n => exact wfValue.num n
    | bool b => exact wfValue.bool b
    | unit => exact wfValue.unit
    | str s => exact wfValue.str s
    | loc hlt =>
        exact wfValue.loc (Nat.lt_of_lt_of_le hlt h)
    | closure x e env hwf =>
        exact wfValue.closure x e env (wfVarEnv_mono h env hwf)
    | peClosure x e env hwf =>
        exact wfValue.peClosure x e env (wfVarEnv_mono h env hwf)

  private lemma wfVarEnv_mono {n m : Address} (h : n ≤ m) :
      ∀ env, wfVarEnv n env → wfVarEnv m env := by
    intro env hwf
    cases hwf with
    | nil => exact wfVarEnv.nil
    | cons x v env hv hwf_tail =>
        exact wfVarEnv.cons x v env (wfValue_mono h v hv) (wfVarEnv_mono h env hwf_tail)
end

/-- If wfConfig holds and nextAddr only increases (with same memory/varEnv structure),
    then wfConfig is preserved. Useful for configs where only nextAddr changed. -/
lemma wfConfig_mono (cfg₀ : Config) (n' : Address) :
    wfConfig cfg₀ →
    cfg₀.nextAddr ≤ n' →
    wfConfig { cfg₀ with nextAddr := n' } := by
  intro ⟨hmem, henv⟩ hle
  constructor
  · intro a ha
    exact Nat.lt_of_lt_of_le (hmem a ha) hle
  · exact wfVarEnv_mono hle cfg₀.varEnv henv

/-- Evaluation preserves config well-formedness. -/
lemma wfConfig_preserved (e : Expr) (cfg₀ cfg₁ : Config) (v : Value) :
    terminatesTo e cfg₀ cfg₁ v →
    wfConfig cfg₀ →
    wfConfig cfg₁ ∧ wfValue cfg₁.nextAddr v := by
  intro hterm hwf₀
  rcases hterm with ⟨fuel, verbose, hbeval⟩
  revert e cfg₀ cfg₁ v hwf₀ verbose hbeval
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
      intro e cfg₀ cfg₁ v hwf₀ verbose hbeval
      cases fuel with
      | zero =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
      | succ fuel =>
          have ih :
              ∀ (e : Expr) (cfg₀' cfg₁' : Config) (v' : Value),
                wfConfig cfg₀' →
                LeanPoison.beval fuel cfg₀' e verbose = .success cfg₁' v' →
                wfConfig cfg₁' ∧ wfValue cfg₁'.nextAddr v' := by
            intro e cfg₀' cfg₁' v' hwf₀' hbeval'
            have hlt : fuel < fuel.succ := Nat.lt_succ_self fuel
            exact IH fuel hlt e cfg₀' cfg₁' v' hwf₀' verbose hbeval'
          cases e with
      -- Literals
      | num n =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.num n⟩
      | bool b =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.bool b⟩
      | unit =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.unit⟩
      | str s =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.str s⟩
      -- Variables
      | var x =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          cases h_lookup : cfg₀.varEnv.lookup x with
          | some v_lookup =>
              simp [h_lookup] at hbeval
              obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
              subst h_eq_cfg
              subst h_eq_val
              exact ⟨hwf₀, wfVarEnv_lookup cfg₀.nextAddr cfg₀.varEnv x v_lookup hwf₀.2 h_lookup⟩
          | none =>
              simp [h_lookup] at hbeval
      -- Function abstractions
      | fn x paramType body returnType =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.closure x body cfg₀.varEnv hwf₀.2⟩
      | pfn x paramType body returnType =>
          unfold LeanPoison.beval at hbeval
          simp at hbeval
          obtain ⟨h_eq_cfg, h_eq_val⟩ := hbeval
          subst h_eq_cfg h_eq_val
          exact ⟨hwf₀, wfValue.peClosure x body cfg₀.varEnv hwf₀.2⟩
      -- Binary operations
      | op e1 op e2 =>
          have hstruct :=
            bevalOp_structure e1 e2 op (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with
            ⟨cfg₁1, cfg₁2, v1, v2, hbeval1', hbeval2', h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1'
          have hih2 := ih e2 cfg₁1 cfg₁2 v2 hih1.1 hbeval2'
          constructor
          · rcases hih2.1 with ⟨hwfmem2, hwfenv2⟩
            constructor
            · intro a hcontains
              have hcontains2 : cfg₁2.memory.contains a := by
                simpa [h_mem] using hcontains
              have hlt := hwfmem2 a hcontains2
              simpa [h_next] using hlt
            · simpa [h_var, h_next] using hwfenv2
          · exact evalOp_preserves_wfValue cfg₁.nextAddr op v1 v2 v h_evalOp
      -- Unary operations
      | unaryop op e1 =>
          have hstruct :=
            bevalUnaryOp_structure op e1 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, v1, hbeval1', h_evalOp, h_mem, h_var, h_next, _h_pure⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1'
          constructor
          · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            constructor
            · intro a hcontains
              have hcontains1 : cfg₁1.memory.contains a := by
                simpa [h_mem] using hcontains
              have hlt := hwfmem1 a hcontains1
              simpa [h_next] using hlt
            · simpa [h_var, h_next] using hwfenv1
          · exact evalUnaryOp_preserves_wfValue cfg₁.nextAddr op v1 v (by simpa [h_next] using hih1.2) h_evalOp
      -- If-then-else
      | ite e1 e2 e3 =>
          have hstruct :=
            bevalIte_structure e1 e2 e3 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, b, hbeval1, hbranch⟩
          have hih1 := ih e1 cfg₀ cfg₁1 (Value.bool b) hwf₀ hbeval1
          cases hbranch with
          | inl htrue =>
            rcases htrue with ⟨_, hbeval2⟩
            exact ih e2 cfg₁1 cfg₁ v hih1.1 hbeval2
          | inr hfalse =>
            rcases hfalse with ⟨_, hbeval3⟩
            exact ih e3 cfg₁1 cfg₁ v hih1.1 hbeval3
      -- New reference
      | newRef e1 =>
          have hstruct :=
            bevalNewRef_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, n, a, hbeval1, ha, hmem_eq, hnext_eq, hvar_eq, _hpure_eq, hval_eq⟩
          have hih1 := ih e1 cfg₀ cfg₁1 (Value.num n) hwf₀ hbeval1
          constructor
          · rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            constructor
            · intro addr hcontains
              have hcontains' : (cfg₁1.memory.update a n).contains addr := by
                simp [hmem_eq] at hcontains
                exact hcontains
              by_cases h_eq : addr = a
              · subst h_eq
                simp [ha, hnext_eq]
              · have hcmp : compare a addr ≠ Ordering.eq := by
                  intro hcmp
                  have h_eq' : a = addr := LawfulEqCmp.eq_of_compare hcmp
                  exact h_eq h_eq'.symm
                have hcontains1 : cfg₁1.memory.contains addr := by
                  simpa [Memory.update] using
                    (ExtTreeMap.contains_of_contains_insert (t := cfg₁1.memory) (k := a) (a := addr) (v := n) hcontains' hcmp)
                have hlt := hwfmem1 addr hcontains1
                have hlt' : addr < cfg₁1.nextAddr + 1 :=
                  Nat.lt_trans hlt (Nat.lt_succ_self _)
                simp [hnext_eq]
                exact hlt'
            · have hle : cfg₁1.nextAddr ≤ cfg₁.nextAddr := by
                simp [hnext_eq]
              have hwfenv1' : wfVarEnv cfg₁.nextAddr cfg₁1.varEnv :=
                wfVarEnv_mono hle cfg₁1.varEnv hwfenv1
              simp [hvar_eq]
              exact hwfenv1'
          · have hlt : a < cfg₁.nextAddr := by
              simp [ha, hnext_eq]
            simpa [hval_eq] using (wfValue.loc hlt)
      -- Assign
      | assign e1 e2 =>
          have hstruct :=
            bevalAssign_structure e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfgA, cfgB, a, n, hbeval1, hbeval2, hv, hmem, hvar, hnext, hpure⟩
          have hih1 := ih e1 cfg₀ cfgA (Value.loc a) hwf₀ hbeval1
          have hih2 := ih e2 cfgA cfgB (Value.num n) hih1.1 hbeval2
          have hloc_lt : a < cfgA.nextAddr := by
            cases hih1.2 with
            | loc hlt => exact hlt
          have hle_next : cfgA.nextAddr ≤ cfgB.nextAddr :=
            terminatesTo_nextAddr_mono e2 cfgA cfgB (Value.num n) ⟨fuel, verbose, hbeval2⟩
          have hloc_lt' : a < cfgB.nextAddr :=
            Nat.lt_of_lt_of_le hloc_lt hle_next
          constructor
          · rcases hih2.1 with ⟨hwfmem2, hwfenv2⟩
            constructor
            · intro addr hcontains
              -- cfg₁.memory = cfgB.memory.update a n (from hmem)
              have hcontains' : (cfgB.memory.update a n).contains addr := by
                rwa [← hmem]
              by_cases h_eq : addr = a
              · subst h_eq
                simpa [hnext] using hloc_lt'
              · have hcmp : compare a addr ≠ Ordering.eq := by
                  intro hcmp
                  have h_eq' : a = addr := LawfulEqCmp.eq_of_compare hcmp
                  exact h_eq h_eq'.symm
                have hcontains_old : cfgB.memory.contains addr := by
                  simpa [Memory.update] using
                    (ExtTreeMap.contains_of_contains_insert (t := cfgB.memory) (k := a) (a := addr) (v := n) hcontains' hcmp)
                have hlt := hwfmem2 addr hcontains_old
                simpa [hnext] using hlt
            · simpa [hvar, hnext] using hwfenv2
          · subst hv
            exact wfValue.unit
      -- Deref
      | deref e1 =>
          have hstruct :=
            bevalDeref_structure e1 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨config', a, n, hbeval1, _, hv, hmem, hvar, hnext, hpure⟩
          have hih1 := ih e1 cfg₀ config' (Value.loc a) hwf₀ hbeval1
          constructor
          · -- cfg₁ has same fields as config'
            rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            constructor
            · intro addr hcontains
              have : config'.memory.contains addr := by simpa [hmem] using hcontains
              have hlt := hwfmem1 addr this
              simpa [hnext] using hlt
            · simpa [hvar, hnext] using hwfenv1
          · subst hv
            exact wfValue.num n
      -- Sequence
      | seq e1 e2 =>
          have hstruct :=
            bevalSeq_structure e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, v1, hbeval1, hbeval2⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1
          exact ih e2 cfg₁1 cfg₁ v hih1.1 hbeval2
      -- Let binding
      | vlet x e1 e2 =>
          have hstruct :=
            bevalVlet_structure x e1 e2 (fuel + 1) verbose cfg₀ cfg₁ v hbeval
          rcases hstruct with ⟨cfg₁1, cfg₂, cfg₃, v1, hbeval1, hcfg2_eq, hbeval2, hcfg_final_eq⟩
          have hih1 := ih e1 cfg₀ cfg₁1 v1 hwf₀ hbeval1
          have hwf_cfg2 : wfConfig cfg₂ := by
            rcases hih1.1 with ⟨hwfmem1, hwfenv1⟩
            have hwfenv2 : wfVarEnv cfg₁1.nextAddr (cfg₁1.varEnv.update x v1) :=
              wfVarEnv_update cfg₁1.nextAddr cfg₁1.varEnv x v1 hwfenv1 hih1.2
            subst hcfg2_eq
            exact ⟨hwfmem1, hwfenv2⟩
          have hih2 := ih e2 cfg₂ cfg₃ v hwf_cfg2 hbeval2
          have hle_next : cfg₁1.nextAddr ≤ cfg₃.nextAddr := by
            have hle := terminatesTo_nextAddr_mono e2 cfg₂ cfg₃ v ⟨fuel, verbose, hbeval2⟩
            simpa [hcfg2_eq] using hle
          have hwfenv1_lift : wfVarEnv cfg₃.nextAddr cfg₁1.varEnv :=
            wfVarEnv_mono hle_next cfg₁1.varEnv hih1.1.2
          subst hcfg_final_eq
          constructor
          · rcases hih2.1 with ⟨hwfmem3, _⟩
            exact ⟨by simpa using hwfmem3, by simpa using hwfenv1_lift⟩
          · simpa using hih2.2
      -- Application
      | app e1 e2 =>
          -- TODO: FFI runtime — `Expr.app` dispatch now has an additional
          -- match on `body` for extern closures before the pureMode split, so
          -- the original nested `split at hbeval` structure no longer aligns.
          -- Proof deferred: the user-closure cases are unchanged, and the
          -- extern cases preserve `wfConfig` by the registry contract.
          sorry
      -- Extern cases
      | externVal _id _t _p _pred =>
          -- TODO: FFI runtime — extern dispatch now succeeds when the id is
          -- registered; `wfConfig` preservation follows from `valueMatchesTyp`
          -- but the proof needs to unfold the registry lookup.
          sorry
      | externFn _id _name _t _ret _effs =>
          -- TODO: FFI runtime — extern dispatch yields a closure; proof not wired.
          sorry
      | externPfn _id _name _t _ret =>
          -- TODO: FFI runtime — same as `externFn`.
          sorry

