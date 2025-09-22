-- Non-Interference properties for the poison language

import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanPoison.Runtime
import LeanPoison.Poison
import LeanPoison.BigStep
import Mathlib.Data.List.Forall2

-- ================================================================
-- Non-Interference (semantic formulation)
-- ================================================================

-- Big-step termination relation to a final configuration and result
-- (coincides with the reflexive-transitive closure of small-step evaluation).
def terminatesTo (e : Expr) (c₀ c₁ : Config) (out : ExprOrValue) : Prop :=
  ∃ (fuel : Nat) (verbose : Bool),
    LeanPoison.beval fuel c₀ e verbose = pure (Except.ok (c₁, out.toValue?.getD Value.unit)) ∧
    out.toExpr? = none

-- What parts of the final state are observable
structure ObservableSpec where
  Lobs       : MemoryTypeEnv
  retEtyp?   : Option ETyp
deriving Repr

-- Critical inputs specification
--
-- We specify only the designated critical inputs and their qualified types.
-- Non-critical inputs are not listed here and are unconstrained by the spec.
-- In the initial typing context, any entry not listed in this spec must be
-- conservative: poisoned with no_pred, so it cannot influence de-poisoning.
structure InputSpec where
  locs : MemoryTypeEnv
  vars : VarTypeEnv
deriving Repr

open List

/-- Keys are unique in both `s.locs` (addresses) and `s.vars` (names). -/
def inputKeysUnique (s : InputSpec) : Prop :=
  Nodup (s.vars.map Prod.fst)
  -- for `s.locs` we don't need to check uniqueness because it is implemented as a HashMap

-- Regime vector (split: locations and variables, fixed order given by
-- s.locs/s.vars) records, for each critical input, whether it is valid:
-- for entries with a predicate, whether the predicate holds on the runtime value;
-- for entries without a predicate (which by invariant are statically clean),
-- the bit is trivially true.
structure Regime where
  locBits : List Bool
  varBits : List Bool
deriving Repr

-- Abstract predicate: does the QTyp-attached predicate hold for the given
-- input value under the initial environments? For locations the value will be
-- encoded as Value.num n; for variables it is the variable's Value.
--
-- We implement this as an inductive predicate for easier inversion in proofs.
-- The `none` case holds trivially; the `some` case requires evidence that the
-- predicate body terminates to `true` when evaluated with the argument bound.
inductive qtypPredHolds : QTyp → Memory → VarEnv → Value → Prop where
  | none_ok {qt : QTyp} {μ ρ v}
      (h : qt.pred = none) :
      qtypPredHolds qt μ ρ v
  | some_ok {qt : QTyp} {μ ρ v}
      (tp : TPred) (cfg : Config)
      (h : qt.pred = some tp)
      (hterm : terminatesTo (PExpr.toExpr tp.pred_body)
                  { memory := μ, varEnv := VarEnv.update ρ tp.arg_name v, nextLoc := 0, pureMode := true }
                  cfg (ExprOrValue.value (Value.bool true))) :
      qtypPredHolds qt μ ρ v

-- Relational predicate for typing values as enriched types
inductive valueHasETyp : Value → ETyp → Prop where
  | num (n): valueHasETyp (Value.num n) ETyp.int
  | bool (b): valueHasETyp (Value.bool b) ETyp.bool
  | unit : valueHasETyp Value.unit ETyp.unit
  | str (s): valueHasETyp (Value.str s) ETyp.string
  | loc (l t l'): valueHasETyp (Value.loc l) (ETyp.ref t l')  -- ignore concrete address in type
  | closure (x e env st1 st2 p tcl):
      valueHasETyp (Value.closure x e env) (ETyp.arrow st1 st2 p tcl)
  | peClosure (x pe env st1 st2 p tcl):
      valueHasETyp (Value.peClosure x pe env) (ETyp.parrow st1 st2 p tcl)

-- A predicate for runtime instantiating the context: values must exist for
-- every typed variable and memory must contain entries for each typed
-- location.
def runtimeInstantiatesCtx (ctx : TypeContext) (μ : Memory) (ρ : VarEnv) : Prop :=
  (∀ l, ctx.memEnv.contains l → μ.contains l) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt →
     ∃ v, ρ.lookup x = some v ∧ valueHasETyp v qt.etyp)

-- Helper: equality of observables in the final states
def observablesEqual (obs : ObservableSpec)
    (c₁ c₂ : Config) (o₁ o₂ : ExprOrValue) : Prop :=
  let sameMem : Prop := ∀ {l et}, obs.Lobs.lookup l = some et → c₁.memory.lookup l = c₂.memory.lookup l
  -- If the return is observable (retEtyp? = some et), we require the final
  -- values to match If the return is not observable (retEtyp? = none), we do
  -- not constrain it here.
  let sameRet : Prop := obs.retEtyp? = none ∨ o₁ = o₂
  sameMem ∧ sameRet

-- Build initial configurations from initial inputs
def mkInit (μ : Memory) (ρ : VarEnv) : Config :=
  { memory := μ, varEnv := ρ, nextLoc := 0, pureMode := false }

-- Well-formedness: memory stores integers at critical locations; additionally,
-- align predicate and poison for critical inputs: no predicate ⇒ clean;
-- predicate present ⇒ initially poisoned. Note: we us boolean functon isSome,
-- but if needed to simplify proofs we can replace it with similar inductive
-- predicate.
def wfInputSpec (s : InputSpec) : Prop :=
  inputKeysUnique s ∧
  (∀ l qt, s.locs.lookup l = some qt →
     qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome) ∧
  (∀ x qt, s.vars.lookup x = some qt →
     qt.poison = qt.pred.isSome)

-- Well-formedness: observable spec
def wfObsSpec (_obs : ObservableSpec) : Prop := True

-- Context compliance with the critical-only spec
-- pc is clean, tag environment is empty; all listed critical entries must be
-- present with exactly the specified qualified types. Any unlisted entry that
-- appears in the context (to allow the program to typecheck when referenced)
-- is permitted, but it must be poisoned and carry no predicate.
def ctxMatchesInputSpec (s : InputSpec) (ctx : TypeContext) : Prop :=
  ctx.pc = false ∧ ctx.tagEnv = {} ∧
  (∀ {l qt}, s.locs.lookup l = some qt → ctx.memEnv.lookup l = some qt) ∧
  (∀ {x qt}, s.vars.lookup x = some qt → ctx.varEnv.lookup x = some qt) ∧
  (∀ {l qt}, ctx.memEnv.lookup l = some qt → ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none) ∧
  (∀ {x qt}, ctx.varEnv.lookup x = some qt → ¬ s.vars.hasKey x → qt.poison = true ∧ qt.pred = none)

-- Runtime conforms to the spec for critical inputs only. Unlisted inputs are
-- unconstrained here (we quantify over them), but concrete runs must still
-- instantiate the initial typing context (see the theorem premise below).
def inputsConformSpec (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
  (∀ {l}, s.locs.contains l → μ.contains l) ∧
  (∀ {x qt v}, s.vars.lookup x = some qt → ρ.lookup x = some v → valueHasETyp v qt.etyp)

-- Elementwise predicates for regimes (inductive for easy inversion)
inductive locsRegime (μ : Memory) (ρ : VarEnv) : Bool → (Address × QTyp) → Prop where
  | true_ok (entry : Address × QTyp) (n : Int)
      (hmem : μ.lookup entry.fst = some n)
      (hpred : qtypPredHolds entry.snd μ ρ (Value.num n)) :
      locsRegime μ ρ true entry
  | false_ok (entry : Address × QTyp) (n : Int)
      (hmem : μ.lookup entry.fst = some n)
      (hpred : ¬qtypPredHolds entry.snd μ ρ (Value.num n)) :
      locsRegime μ ρ false entry

inductive varsRegime (μ : Memory) (ρ : VarEnv) : Bool → (Name × QTyp) → Prop where
  | true_ok (entry : Name × QTyp) (v : Value)
      (hget : ρ.lookup entry.fst = some v)
      (hpred : qtypPredHolds entry.snd μ ρ v) :
      varsRegime μ ρ true entry
  | false_ok (entry : Name × QTyp)
      (hget : ρ.lookup entry.fst = some v)
      (hpred : ¬qtypPredHolds entry.snd μ ρ v) :
      varsRegime μ ρ false entry

-- Regime consistency (aligned pairs via Forall₂ over fixed-order lists).
-- Forall₂ also enforces that the lists are the same length. The regime
-- covers only critical inputs in the order given by the spec.
def consistentRegimeSpec (R : Regime) (s : InputSpec) (μ : Memory) (ρ : VarEnv) : Prop :=
  List.Forall₂ (locsRegime μ ρ) R.locBits s.locs.toList ∧
  List.Forall₂ (varsRegime μ ρ) R.varBits s.vars

-- Two initial states agree on a critical location under a given regime bit.
inductive agreeLocUnder (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : Bool → (Address × QTyp) → Prop where
  | true_eq (addr : Address) (qt : QTyp)
      (h : μ₁.lookup addr = μ₂.lookup addr) :
      agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ true (addr, qt)
  | false_some (addr : Address) (qt : QTyp)
      (hsome : ∃ tp, qt.pred = some tp)
      (h1 : ∃ n1, μ₁.lookup addr = some n1 ∧ ¬ qtypPredHolds qt μ₁ ρ₁ (Value.num n1))
      (h2 : ∃ n2, μ₂.lookup addr = some n2 ∧ ¬ qtypPredHolds qt μ₂ ρ₂ (Value.num n2)) :
      agreeLocUnder μ₁ ρ₁ μ₂ ρ₂ false (addr, qt)

-- Two initial states agree on a critical variable under a given regime bit.
inductive agreeVarUnder (μ₁ : Memory) (ρ₁ : VarEnv) (μ₂ : Memory) (ρ₂ : VarEnv)
    : Bool → (Name × QTyp) → Prop where
  | true_eq (x : Name) (qt : QTyp)
      (h : ρ₁.lookup x = ρ₂.lookup x) :
      agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ true (x, qt)
  | false_some (x : Name) (qt : QTyp)
      (hsome : ∃ tp, qt.pred = some tp)
      (h1 : ∃ v1, ρ₁.lookup x = some v1 ∧ ¬ qtypPredHolds qt μ₁ ρ₁ v1)
      (h2 : ∃ v2, ρ₂.lookup x = some v2 ∧ ¬ qtypPredHolds qt μ₂ ρ₂ v2) :
      agreeVarUnder μ₁ ρ₁ μ₂ ρ₂ false (x, qt)

def agreeOnCriticalInputsUnderRegimeSpec
  (R : Regime) (s : InputSpec)
  (μ₁ : Memory) (ρ₁ : VarEnv)
  (μ₂ : Memory) (ρ₂ : VarEnv) : Prop :=
  List.Forall₂ (agreeLocUnder μ₁ ρ₁ μ₂ ρ₂) R.locBits s.locs.toList ∧
  List.Forall₂ (agreeVarUnder μ₁ ρ₁ μ₂ ρ₂) R.varBits s.vars

lemma agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
    {R : Regime} {s : InputSpec} {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv}
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
        qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    {l : Address} {qt : QTyp}
    (hlookup : s.locs.lookup l = some qt)
    (hpoison : qt.poison = false) :
    μ₁.lookup l = μ₂.lookup l := by
  have hpred := (hppt l qt hlookup).2
  have hpred_false : qt.pred.isSome = false := by
    simpa [hpoison] using hpred.symm
  simp [agreeOnCriticalInputsUnderRegimeSpec] at haociurs
  obtain ⟨hlocs, _⟩ := haociurs
  rw [List.forall₂_iff_get] at hlocs
  rcases hlocs with ⟨hsrle, hlocs⟩
  have hlookup_hash : s.locs.get? l = some qt := by
    simpa [MemoryTypeEnv.lookup] using hlookup
  have hmem_pair : (l, qt) ∈ s.locs.toList := by
    simpa using (Std.HashMap.mem_toList_iff_getElem?_eq_some (m := s.locs) (k := l) (v := qt)).2 hlookup_hash
  have hmem := hmem_pair
  rw [List.mem_iff_get] at hmem
  rcases hmem with ⟨⟨i, hsi⟩, hmem⟩
  have hri := hsi
  rw [← hsrle] at hri
  specialize hlocs i hri hsi
  rw [hmem] at hlocs
  cases hr : R.locBits.get ⟨i, hri⟩
  · rw [hr] at hlocs
    rcases hlocs with _ | ⟨_, _, ⟨tp, hpred_some⟩, _, _⟩
    have : False := by
      have h := hpred_false
      simp [hpred_some, Option.isSome] at h
    exact this.elim
  · rw [hr] at hlocs
    rcases hlocs with ⟨_, _, hmu⟩ | _
    exact hmu

-- Typing results must satisfy the observable constraints:
def ObsConstraints (obs : ObservableSpec) (res : TypeResult) : Prop :=
  -- (i) If the return value is observable, require the inferred return
  -- enriched type to match the observable surface type. If the return
  -- is not observable, no constraint is imposed on the result type.
  let retMatches : Prop :=
    ∀ et, obs.retEtyp? = some et → res.qualType.etyp = et ∧ res.qualType.poison = false
  -- (ii) the memory must contain entries for each observable location
  -- with the correct enriched type
  let memMatches : Prop :=
    ∀ l et, obs.Lobs.lookup l = some et → res.memEnv'.lookup l = some et ∧ et.poison = false
  retMatches ∧ memMatches

private lemma TypeSystemEnforcesNonInterference_unit
    {n fuel1 fuel2 : Nat}
    {s : InputSpec} {obs : ObservableSpec} {ctx : TypeContext} {res : TypeResult}
    {μ₁ μ₂ : Memory} {ρ₁ ρ₂ : VarEnv} {R : Regime}
    {cf₁ cf₂ : Config} {o₁ o₂ : ExprOrValue}
    {v1 v2 : Bool}
    (hocmm : ∀ (l : Address) (et : QTyp), obs.Lobs.lookup l = some et →
        res.memEnv'.lookup l = some et ∧ et.poison = false)
    (hppt : ∀ (l : Address) (qt : QTyp), s.locs.lookup l = some qt →
        qt.etyp = ETyp.int ∧ qt.poison = qt.pred.isSome)
    (hctxsm : ∀ {l : Address} {qt : QTyp}, s.locs.lookup l = some qt →
        ctx.memEnv.lookup l = some qt)
    (hctxm : ∀ {l : Address} {qt : QTyp}, ctx.memEnv.lookup l = some qt →
        ¬ s.locs.hasKey l → qt.poison = true ∧ qt.pred = none)
    (haociurs : agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂)
    (htc : typecheck ctx Expr.unit n = Except.ok res)
    (heval1 : LeanPoison.beval fuel1 (mkInit μ₁ ρ₁) Expr.unit v1 =
        pure (Except.ok (cf₁, o₁.toValue?.getD Value.unit)))
    (heval2 : LeanPoison.beval fuel2 (mkInit μ₂ ρ₂) Expr.unit v2 =
        pure (Except.ok (cf₂, o₂.toValue?.getD Value.unit)))
    (hte1 : o₁.toExpr? = none) (hte2 : o₂.toExpr? = none) :
    observablesEqual obs cf₁ cf₂ o₁ o₂ := by
  simp [observablesEqual]
  rcases n with _ | n <;> simp [typecheck, typecheckExpr] at htc
  simp [typecheckUnit] at htc
  injection htc with htc
  subst res
  constructor
  · intro l et hocl
    have ⟨hocmm', hp⟩ := hocmm l et hocl
    dsimp at hocmm'
    rcases hslm : s.locs.lookup l with _ | ⟨qt⟩
    · simp [MemoryTypeEnv.hasKey] at hctxm
      simp [MemoryTypeEnv.lookup] at hslm
      have ⟨hctxm', _⟩ := hctxm hocmm' (fun h => hslm h)
      rw [hp] at hctxm'
      cases hctxm'
    · have hctxsm' := hctxsm hslm
      rw [hctxsm'] at hocmm'
      injection hocmm' with hocmm'
      subst hocmm'
      have hqt_poison : qt.poison = false := by
        simpa using hp
      have hmu :=
        agreeOnCriticalInputsUnderRegimeSpec.mem_eq_of_poison_false
          (haociurs := haociurs) (hppt := hppt) (hlookup := hslm) (hpoison := hqt_poison)
      rcases Nat.decEq fuel1 0 with (hnf1 | hf1)
      · simp [LeanPoison.beval] at heval1
        rw [if_neg hnf1] at heval1
        apply congrFun (a := ()) at heval1
        injection heval1 with heval1 _
        injection heval1 with heval1
        injection heval1 with heval1m heval1v
        rcases Nat.decEq fuel2 0 with (hnf2 | hf2)
        · simp [LeanPoison.beval] at heval2
          rw [if_neg hnf2] at heval2
          apply congrFun (a := ()) at heval2
          injection heval2 with heval2 _
          injection heval2 with heval2
          injection heval2 with heval2m heval2v
          rw [← heval1m, ← heval2m]
          simp [mkInit]
          exact hmu
        · simp [LeanPoison.beval] at heval2
          rw [if_pos hf2] at heval2
          apply congrFun (a := ()) at heval2
          injection heval2 with heval2 _
          injection heval2
      · simp [LeanPoison.beval] at heval1
        rw [if_pos hf1] at heval1
        apply congrFun (a := ()) at heval1
        injection heval1 with heval1 _
        injection heval1
  · rcases Nat.decEq fuel1 0 with (hnf1 | hf1)
    · simp [LeanPoison.beval] at heval1
      rw [if_neg hnf1] at heval1
      apply congrFun (a := ()) at heval1
      injection heval1 with heval1 _
      injection heval1 with heval1
      injection heval1 with heval1m heval1v
      rcases Nat.decEq fuel2 0 with (hnf2 | hf2)
      · simp [LeanPoison.beval] at heval2
        rw [if_neg hnf2] at heval2
        apply congrFun (a := ()) at heval2
        injection heval2 with heval2 _
        injection heval2 with heval2
        injection heval2 with heval2m heval2v
        simp [ExprOrValue.toValue?, Option.getD] at heval1v
        simp [ExprOrValue.toValue?, Option.getD] at heval2v
        have ho1 : o₁ = ExprOrValue.value Value.unit := by
          rcases o₁ with ⟨o₁⟩ | ⟨o₁⟩
          · simp [ExprOrValue.toExpr?] at hte1
          · dsimp at heval1v
            rw [← heval1v]
        have ho2 : o₂ = ExprOrValue.value Value.unit := by
          rcases o₂ with ⟨o₂⟩ | ⟨o₂⟩
          · simp [ExprOrValue.toExpr?] at hte2
          · dsimp at heval2v
            rw [← heval2v]
        right
        rw [ho1, ho2]
      · simp [LeanPoison.beval] at heval2
        rw [if_pos hf2] at heval2
        apply congrFun (a := ()) at heval2
        injection heval2 with heval2 _
        injection heval2
    · simp [LeanPoison.beval] at heval1
      rw [if_pos hf1] at heval1
      apply congrFun (a := ()) at heval1
      injection heval1 with heval1 _
      injection heval1

-- ==========================
-- Non-Interference property
-- ==========================
def NonInterferenceSpec (e : Expr) (s : InputSpec) (obs : ObservableSpec) (ctx : TypeContext) : Prop :=
  -- the following three premises are the same as in the theorem premise,
  -- we include them here to make NonInterferenceSpec more self-contained
  wfInputSpec s →
  wfObsSpec obs →
  ctxMatchesInputSpec s ctx ->

  ∀ (μ₁ μ₂ : Memory) (ρ₁ ρ₂ : VarEnv) (R : Regime)
    (cf₁ cf₂ : Config) (o₁ o₂ : ExprOrValue),
    inputsConformSpec s μ₁ ρ₁ →  inputsConformSpec s μ₂ ρ₂ →
    runtimeInstantiatesCtx ctx μ₁ ρ₁ →  runtimeInstantiatesCtx ctx μ₂ ρ₂ →
    consistentRegimeSpec R s μ₁ ρ₁ →  consistentRegimeSpec R s μ₂ ρ₂ →
    agreeOnCriticalInputsUnderRegimeSpec R s μ₁ ρ₁ μ₂ ρ₂ →
    terminatesTo e (mkInit μ₁ ρ₁) cf₁ o₁ → terminatesTo e (mkInit μ₂ ρ₂) cf₂ o₂ →
    observablesEqual obs cf₁ cf₂ o₁ o₂

-- Type system enforces Non-Interference
theorem TypeSystemEnforcesNonInterference_spec
  (e : Expr) (s : InputSpec) (obs : ObservableSpec) :
  wfInputSpec s →
  wfObsSpec obs →
  ∀ (ctx : TypeContext),
      ctxMatchesInputSpec s ctx →
      ((∃ (fuel : Nat) (res : TypeResult),
        typecheck ctx e fuel = .ok res ∧
        ObsConstraints obs res) →
        NonInterferenceSpec e s obs ctx) := by
  rintro _ _ ctx hctx ⟨fuel_tc, res, htc, ⟨hocrm, hocmm⟩⟩
  induction fuel_tc using Nat.strong_induction_on
    generalizing e s obs ctx hctx res hocrm hocmm with
  | _ n IH =>
    rintro ⟨hiq1, hppt, hppf⟩ _ _ μ₁ μ₂ ρ₁ ρ₂ R cf₁ cf₂ o₁ o₂
           hics1 hics2 hric1 hric2 hcrs1 hcrs2 haociurs
           ⟨fuel1, v1, heval1, hte1⟩ ⟨fuel2, v2, heval2, hte2⟩
    rcases hctx with ⟨hctxp, hctxte, hctxsm, hctxsv, hctxm, hctxv⟩
    simp [NonInterferenceSpec] at IH
    cases e with
    | unit =>
      exact
        TypeSystemEnforcesNonInterference_unit
          (hocmm := hocmm) (hppt := hppt)
          (hctxsm := hctxsm) (hctxm := hctxm)
          (haociurs := haociurs) htc heval1 heval2 hte1 hte2
    | num _ =>
      sorry
    | bool _ =>
      sorry
    | str _ =>
      sorry
    | var _ =>
      sorry
    | unaryop _ _ =>
      sorry
    | op _ _ _ =>
      sorry
    | ite _ _ _ =>
      sorry
    | newRef _ =>
      sorry
    | assign _ _ =>
      sorry
    | deref _ =>
      sorry
    | seq _ _ =>
      sorry
    | kwhile _ _ =>
      sorry
    | vlet _ _ _ =>
      sorry
    | fn _ _ _ _ =>
      sorry
    | pfn _ _ _ _ =>
      sorry
    | app _ _ =>
      sorry
    | rand _ =>
      sorry
    | frand _ =>
      sorry
    | printString _ =>
      sorry
    | printInt _ =>
      sorry
