/-
  PredSatLawsCellWitness.lean — `PredSatLaws` is met by a relation that reads a cell.

  The guard `v => v > !a` with `a : ref {0}` reads the cell at location `0`. The
  relation `cellSat` reads that cell through the realisation map: the checked
  value is a number greater than the content of the address the map gives to
  location `0`. This module proves that `cellSat` meets both laws of
  `PredSatLaws` (`match_iff` against the real `matchGuard`, and `mem_footprint`)
  for the tag meaning that interprets tag `0` as this guard, with no further
  hypothesis (`cellSat_lawful`). It exhibits a context that respects the tag
  meaning, in which `matchGuard` selects the guard for the test `y > !a`, and
  two states in which the relation differs (`match_exercised`).

  Two guards that `matchGuard` never selects in a context that respects their
  tag meaning: `v => v > !a` with `a : ref {0, 1}` (`TwoTargets`) and
  `v => !v > 0`, which reads through its own argument (`DerefArg`). For such a
  tag meaning every relation meets `match_iff`, and a constant relation meets
  both laws; for `v => !v > 0` the law `mem_footprint` makes the relation
  independent of the state (`DerefArg.footprint_forces_constant`).

  The module is a leaf of the import graph; nothing on the fault-robustness proof
  path depends on it.
-/

import LeanProofs.MatchGuardLemmas

open Std

namespace PredSatLawsCellWitness



/-- The guard `v => v > !a`. -/
def body : PExpr := PExpr.op (PExpr.var "v") Op.gt (PExpr.deref (PExpr.var "a"))

def refQt (ls : LocSet) : QTyp :=
  { etyp := ETyp.ref ls, poison := false, pred := Predicate.noPred }

def s0 : LocSet := LocSet.singleton 0
def s01 : LocSet := (LocSet.singleton 0).insert 1

/-- The guard captures `a : ref {0}`. -/
def cap : CapturedVarEnv := [("a", refQt s0)]

def desc : GuardDesc := { argName := "v", body := body, capEnv := cap }

/-- The tag table: tag `0` is `v => v > !a` with `a : ref {0}`. -/
def tm1 : TagMeaning := (∅ : TagMeaning).update 0 desc

private theorem tm1_lookup_eq {k : Tag} {d : GuardDesc} (h : tm1.lookup k = some d) :
    k = 0 ∧ d = desc := by
  by_cases hk : (0 : Tag) = k
  · subst hk
    exact ⟨rfl, by simpa [tm1, TagMeaning.lookup, TagMeaning.update] using h.symm⟩
  · simp [tm1, TagMeaning.lookup, TagMeaning.update, hk] at h

private theorem tm1_lookup_zero : tm1.lookup 0 = some desc := by
  simp [tm1, TagMeaning.lookup, TagMeaning.update]

/-- Two cells, `0` and `1`, clean and without predicates. -/
def memEnv01 : MemoryTypeEnv :=
  ((∅ : MemoryTypeEnv).insert 0 ⟨false, Predicate.noPred⟩).insert 1 ⟨false, Predicate.noPred⟩

def qtY : QTyp :=
  { etyp := ETyp.int, poison := true, pred := Predicate.guardClosure 0 "v" body cap }

/-- `a : ref {0}, y : {v : int | v > !a}`. -/
def ctx1 : TypeContext :=
  { pc := false, regime := ∅, memEnv := memEnv01,
    varEnv := ((∅ : VarTypeEnv).update "a" (refQt s0)).update "y" qtY,
    tagEnv := ∅, nextLoc := 2, nextTag := 1, pureCtx := false }

/-- The test `y > !a`. -/
def cond : Expr := Expr.op (Expr.var "y") Op.gt (Expr.deref (Expr.var "a"))

/-- The guard of `y` matches the condition in `ctx1`. The elaborator does not
    reduce `guardScopeAgrees`; the kernel does (`decide +kernel`, nothing beyond
    the three standard ones). -/
private theorem cond_matches_bool :
    (match matchGuard cond ctx1.memEnv ctx1.varEnv 10 with
      | .ok (k, _) => k == 0
      | .error _ => false) = true := by
  decide +kernel

theorem cond_matches : ∃ deps, matchGuard cond ctx1.memEnv ctx1.varEnv 10 = .ok (0, deps) := by
  have h := cond_matches_bool
  revert h
  generalize matchGuard cond ctx1.memEnv ctx1.varEnv 10 = r
  rcases r with _ | ⟨k, deps⟩
  · intro h; simp at h
  · intro h
    simp only [beq_iff_eq] at h
    exact ⟨deps, by rw [h]⟩

private theorem lookup_ctx1 {x : Name} {qt : QTyp} (h : ctx1.varEnv.lookup x = some qt) :
    (x = "y" ∧ qt = qtY) ∨ (x = "a" ∧ qt = refQt s0) := by
  simp only [ctx1] at h
  by_cases hy : x = "y"
  · subst hy
    rw [VarTypeEnv_lookup_update_eq] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [VarTypeEnv_lookup_update_ne _ "y" x qtY hy] at h
    by_cases ha : x = "a"
    · subst ha
      rw [VarTypeEnv_lookup_update_eq] at h
      exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
    · rw [VarTypeEnv_lookup_update_ne _ "a" x _ ha] at h
      simp [VarTypeEnv.lookup] at h

private theorem memLookup01 {l : Loc} {memQt : QTyp} (h : memEnv01.lookup l = some memQt) :
    memQt = { etyp := ETyp.int, poison := false, pred := Predicate.noPred } := by
  simp only [memEnv01, MemoryTypeEnv.lookup] at h
  rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert,
    Std.ExtTreeMap.getElem?_insert] at h
  split at h
  · simp at h; exact h.symm
  · split at h
    · simp at h; exact h.symm
    · simp at h

theorem ctx1_wf : wfTagMeaningCtx tm1 ctx1 := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hdeep
  rcases hdeep with ⟨qt, k, d, hin, hdesc⟩
  cases hin with
  | inVar _ _ x _ qtRoot hlookup hinq =>
    rcases lookup_ctx1 hlookup with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have hqt : qt = qtY :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [qtY, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, qtY] at hdesc
      obtain ⟨rfl, rfl⟩ := hdesc
      exact tm1_lookup_zero
    · have hqt : qt = refQt s0 :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [refQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, refQt] at hdesc
  | inMem _ _ l _ qtRoot hlookup hinq =>
    have hroot := memLookup01 hlookup
    subst hroot
    have hqt := QTypInQTyp_eq_of_nonFunctionTarget hinq
      (by simp [ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
    subst hqt
    simp [qtypGuardDesc?] at hdesc

/-- One memory: address `0` holds `0`, address `1` holds `10`. -/
def μ01 : Memory := ((∅ : Memory).insert 0 0).insert 1 10

/-- Location `0` at address `addr`. -/
def θat (addr : Address) : RealizationMap := (∅ : RealizationMap).insert 0 addr

def rho (addr : Address) : VarEnv := [("y", Value.num 5), ("a", Value.loc addr)]

def cfgOf (addr : Address) : Config :=
  { memory := μ01, varEnv := rho addr, nextAddr := 2, pureMode := false, registry := default }

private theorem θat_lookup {addr : Address} {l : Loc} {a : Address} (h : (θat addr).lookup l = some a) :
    l = 0 ∧ a = addr := by
  simp only [θat, RealizationMap.lookup] at h
  by_cases hl : l = 0
  · subst hl
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self] at h
    simp at h
    exact ⟨rfl, h.symm⟩
  · rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at h
    have hc : ¬ compare 0 l = Ordering.eq := by
      intro hc; exact hl ((Nat.compare_eq_eq).1 hc).symm
    simp [hc] at h

private theorem θat_zero (addr : Address) : (θat addr).lookup 0 = some addr := by
  simp [θat, RealizationMap.lookup]

private theorem ric (addr : Address) (hμ : μ01.contains addr = true) :
    runtimeInstantiatesCtx ctx1 μ01 (rho addr) (θat addr) := by
  refine ⟨?_, ?_⟩
  · intro l a h
    obtain ⟨rfl, rfl⟩ := θat_lookup h
    exact ⟨by simp [ctx1, memEnv01], hμ⟩
  · intro x qt h
    rcases lookup_ctx1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Value.num 5, rfl, valueHasETyp.num _⟩
    · refine ⟨Value.loc addr, rfl, ?_⟩
      exact valueHasETyp.loc (l := 0) (θat_zero addr) (by simp [s0, LocSet.singleton])

private theorem cond_runs_0 : terminatesTo cond (cfgOf 0) (cfgOf 0) (Value.bool true) := by
  refine ⟨5, false, ?_⟩
  have hy : VarEnv.lookup (rho 0) "y" = some (Value.num 5) := rfl
  have ha : VarEnv.lookup (rho 0) "a" = some (Value.loc 0) := rfl
  have hm : μ01[(0 : Address)]? = some 0 := by
    simp only [μ01, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_empty]
    decide
  simp [cond, LeanPoison.beval, LeanPoison.evalOp, cfgOf, hy, ha, hm]

private theorem cond_runs_1 : terminatesTo cond (cfgOf 1) (cfgOf 1) (Value.bool false) := by
  refine ⟨5, false, ?_⟩
  have hy : VarEnv.lookup (rho 1) "y" = some (Value.num 5) := rfl
  have ha : VarEnv.lookup (rho 1) "a" = some (Value.loc 1) := rfl
  have hm : μ01[(1 : Address)]? = some 10 := by
    simp only [μ01, Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_empty]
    decide
  simp [cond, LeanPoison.beval, LeanPoison.evalOp, cfgOf, hy, ha, hm]

/-- In `ctx1` the only owner of a guard closure is `y`, whose value is `5`. -/
private theorem owner_value {addr : Address} {θ : RealizationMap} {k : Tag} {v : Value}
    (h :
      (∃ (x : Name) (qt : QTyp) (arg_name : Name) (pred_body : PExpr)
          (var_env : CapturedVarEnv),
          ctx1.varEnv.lookup x = some qt ∧
          qt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          (rho addr).lookup x = some v)
      ∨
      (∃ (x : Name) (qt memQt : QTyp) (ls : LocSet) (l0 : Loc) (a : Address) (n : Int)
          (arg_name : Name) (pred_body : PExpr) (var_env : CapturedVarEnv),
          ctx1.varEnv.lookup x = some qt ∧
          qt.etyp = ETyp.ref ls ∧
          l0 ∈ ls ∧
          ctx1.memEnv.lookup l0 = some memQt ∧
          memQt.pred = Predicate.guardClosure k arg_name pred_body var_env ∧
          θ.lookup l0 = some a ∧
          μ01.lookup a = some n ∧
          v = Value.num n)) :
    v = Value.num 5 := by
  rcases h with ⟨x, qt, _, _, _, hlookup, hpred, hρ⟩ |
    ⟨_, _, memQt, _, _, _, _, _, _, _, _, _, _, hmem, hpred, _⟩
  · rcases lookup_ctx1 hlookup with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hl : (rho addr).lookup "y" = some (Value.num 5) := rfl
      rw [hl] at hρ
      exact (Option.some.inj hρ).symm
    · simp [refQt] at hpred
  · have hroot := memLookup01 hmem
    subst hroot
    simp at hpred

/-! ## `cellSat` meets both laws -/

/-- The checked value is a number greater than the content of the cell at which
    the map puts location `0`. -/
def cellSat : PredSat := fun k θ μ v =>
  k = 0 ∧ ∃ (a : Address) (n m : Int),
    θ.lookup 0 = some a ∧ μ.lookup a = some n ∧ v = Value.num m ∧ n < m

private theorem equalWithEnvs_var_v_deref_v {e1 e2 : CapturedVarEnv} :
    ∀ (pe : PExpr) (f : Nat),
      PExpr.equalWithEnvs (PExpr.var "v") e1 pe e2
        (some ("v", PExpr.deref (PExpr.var "v"))) f = true → False := by
  intro pe
  induction pe with
  | deref pe' ih =>
    intro f h
    rcases f with _ | _ | f
    · simp [PExpr.equalWithEnvs] at h
    · simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h
    · simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h
      exact ih f h
  | _ =>
    intro f h
    rcases f with _ | _ | f <;> simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h

private theorem equalWithEnvs_v_var {e1 e2 : CapturedVarEnv} {x : Name} {pe : PExpr} {f : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var "v") e1 pe e2 (some ("v", PExpr.var x)) f = true) :
    pe = PExpr.var x := by
  rcases f with _ | _ | f
  · simp [PExpr.equalWithEnvs] at h
  · by_cases hx : x = "v"
    · subst hx
      cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
  · by_cases hx : x = "v"
    · subst hx
      cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]

private theorem equalWithEnvs_v_deref {e1 e2 : CapturedVarEnv} {x : Name} {pe : PExpr} {f : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var "v") e1 pe e2
      (some ("v", PExpr.deref (PExpr.var x))) f = true) :
    pe = PExpr.deref (PExpr.var x) := by
  by_cases hx : x = "v"
  · subst hx
    exact (equalWithEnvs_var_v_deref_v pe f h).elim
  · rcases f with _ | _ | _ | f
    · simp [PExpr.equalWithEnvs] at h
    · simp [PExpr.equalWithEnvs, BEq.beq, beqPExpr] at h
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
    · cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
      rename_i pe'
      cases pe' <;> simp_all

private theorem equalWithEnvs_body {e1 e2 : CapturedVarEnv} {arg pe : PExpr} {f : Nat}
    (h : PExpr.equalWithEnvs body e1 pe e2 (some ("v", arg)) f = true) :
    ∃ pe1 f', pe = PExpr.op pe1 Op.gt (PExpr.deref (PExpr.var "a")) ∧
      PExpr.equalWithEnvs (PExpr.var "v") e1 pe1 e2 (some ("v", arg)) f' = true := by
  rcases f with _ | f
  · simp [PExpr.equalWithEnvs] at h
  · cases pe with
    | op p1 o p2 =>
      simp only [body, PExpr.equalWithEnvs, Bool.and_eq_true] at h
      obtain ⟨⟨ho, h1⟩, h2⟩ := h
      refine ⟨p1, f, ?_, h1⟩
      have ho' : o = Op.gt := by
        cases o <;> revert ho <;> decide
      subst ho'
      rcases f with _ | _ | f
      · simp [PExpr.equalWithEnvs] at h2
      · cases p2 <;> simp [PExpr.equalWithEnvs] at h2
      · cases p2 with
        | deref q =>
          cases q <;> simp_all [PExpr.equalWithEnvs, BEq.beq]
        | _ => simp [PExpr.equalWithEnvs] at h2
    | _ => simp [body, PExpr.equalWithEnvs] at h

private theorem toPExpr?_var {e : Expr} {x : Name}
    (h : e.toPExpr? = some (PExpr.var x)) : e = Expr.var x := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_deref {e : Expr} {pe : PExpr}
    (h : e.toPExpr? = some (PExpr.deref pe)) : ∃ e', e = Expr.deref e' ∧ e'.toPExpr? = some pe := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_op {e : Expr} {p1 p2 : PExpr} {o : Op}
    (h : e.toPExpr? = some (PExpr.op p1 o p2)) :
    ∃ e1 e2, e = Expr.op e1 o e2 ∧ e1.toPExpr? = some p1 ∧ e2.toPExpr? = some p2 := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

/-- The guard's dependency set, whenever it is computed, contains location `0`. -/
private theorem deps_mem_zero {fuel : Nat} {deps : Deps}
    (h : extractDepsFromPred (Predicate.guardClosure 0 "v" body cap) fuel = .ok deps) :
    0 ∈ deps := by
  rcases fuel with _ | _ | _ | f
  all_goals simp [extractDepsFromPred, extractDepsFromPred.extractDepsFromPExpr, body,
    cap, refQt, s0, VarTypeEnv.ofCaptured] at h
  all_goals simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure, bind, Except.bind] at h
  subst h
  simp [LocSet.union, LocSet.singleton, LocSet.empty]

/-- The in-scope rule gives `a` its captured type in the context. -/
private theorem a_in_scope {S : VarTypeEnv} (h : GuardInScope S "v" body cap) :
    S.lookup "a" = some (refQt s0) := by
  obtain ⟨qt, _, _, hcap, hS, _, _, _⟩ := h.reads "a" (by simp [PExpr.freeVars, body])
  have : qt = refQt s0 := by
    simpa [cap, VarTypeEnv.ofCaptured, VarTypeEnv.lookup] using hcap.symm
  subst this
  exact hS

/-- In a context where `a` is `ref {0}`, `a` holds the address of location `0`. -/
private theorem a_at_zero {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    {a0 : Address}
    (hA : ctx.varEnv.lookup "a" = some (refQt s0))
    (hric : runtimeInstantiatesCtx ctx μ ρ θ)
    (hρ : ρ.lookup "a" = some (Value.loc a0)) :
    θ.lookup 0 = some a0 := by
  obtain ⟨w, hw, hty⟩ := hric.2 hA
  rw [hρ] at hw
  cases hw
  cases hty with
  | loc hl hin =>
    rename_i l
    have : l = 0 := by
      simp only [s0, LocSet.singleton, Std.ExtTreeSet.mem_insert, Std.ExtTreeSet.not_mem_empty,
        or_false] at hin
      exact ((Nat.compare_eq_eq).1 hin).symm
    subst this
    exact hl

private theorem cellSat_iff {θ : RealizationMap} {μ : Memory} {a0 : Address} {n m : Int} {b : Bool}
    (hθ : θ.lookup 0 = some a0) (hμ : μ.lookup a0 = some n)
    (hev : LeanPoison.evalOp Op.gt (Value.num m) (Value.num n) = some (Value.bool b)) :
    (b = true ↔ cellSat 0 θ μ (Value.num m)) := by
  simp only [LeanPoison.evalOp, Option.some.injEq, Value.bool.injEq] at hev
  subst hev
  constructor
  · intro h
    exact ⟨rfl, a0, n, m, hθ, hμ, rfl, by simpa using h⟩
  · rintro ⟨-, a, n', m', ha, hn, hv, hlt⟩
    rw [hθ] at ha
    cases ha
    rw [hμ] at hn
    cases hn
    cases hv
    simpa using hlt

/-- **`cellSat` meets the candidate laws for `tm1`**, against the real
    `matchGuard`, with no hypothesis beyond the law's own. -/
theorem cellSat_lawful : PredSatLaws cellSat tm1 := by
  refine ⟨?_, ?_⟩
  · intro condition ctx fuel k deps μ ρ θ addr pm registry cfg b hwf hmatch hric hterm
    obtain ⟨pe, hpe, hown⟩ := matchGuard_ok_matched_owner_inScope ctx condition k deps hmatch
    rcases hown with
      ⟨x, qt, arg, pbody, pcap, hlookup, hpred, heq, hscope⟩ |
      ⟨x, qt, ls, arg, pbody, pcap, hlookup, hetyp, _hpois, hne, hall, heq, hscope⟩
    · obtain ⟨rfl, hdesc⟩ := tm1_lookup_eq (hwf.1
        (GuardDescInEnvsDeep.intro qt k ⟨arg, pbody, pcap⟩
          (QTypInEnvs.inVar ctx.varEnv ctx.memEnv x qt qt hlookup (QTypInQTyp.self qt))
          (by simp [qtypGuardDesc?, hpred])))
      simp only [desc, GuardDesc.mk.injEq] at hdesc
      obtain ⟨rfl, rfl, rfl⟩ := hdesc
      have hA := a_in_scope hscope
      obtain ⟨pe1, f', rfl, h1⟩ := equalWithEnvs_body heq
      have hpe1 := equalWithEnvs_v_var h1
      subst hpe1
      obtain ⟨e1, e2, rfl, he1, he2⟩ := toPExpr?_op hpe
      have := toPExpr?_var he1
      subst this
      obtain ⟨e2', rfl, he2'⟩ := toPExpr?_deref he2
      have := toPExpr?_var he2'
      subst this
      obtain ⟨c1, v1, v2, ht1, ht2, hev, _, _⟩ := terminatesTo_op_inv' _ _ _ _ _ _ hterm
      obtain ⟨v', hρ, rfl, hv1⟩ := terminatesTo_var_inv' _ _ _ _ ht1
      subst hv1
      obtain ⟨c2, a0, n, ht2', hμ, rfl, _, _, _, _⟩ := terminatesTo_deref_inv' _ _ _ _ ht2
      obtain ⟨va, hρa, rfl, hva⟩ := terminatesTo_var_inv' _ _ _ _ ht2'
      subst hva
      have hθ := a_at_zero hA hric hρa
      cases v1 with
      | num m =>
        exact ⟨Value.num m, Or.inl ⟨x, qt, "v", body, cap, hlookup, hpred, hρ⟩,
          cellSat_iff hθ hμ hev⟩
      | _ => simp [LeanPoison.evalOp] at hev
    · obtain ⟨l, hl⟩ : ∃ l, l ∈ ls := by
        have hlist : ls.toList.isEmpty = false := by
          rw [ExtTreeSet.isEmpty_toList]; exact hne
        cases htl : ls.toList with
        | nil => simp [htl] at hlist
        | cons a as => exact ⟨a, ExtTreeSet.mem_toList.mp (by simp [htl])⟩
      obtain ⟨memQt, hmem, hpredm⟩ := hall l hl
      obtain ⟨rfl, hdesc⟩ := tm1_lookup_eq (hwf.1
        (GuardDescInEnvsDeep.intro memQt k ⟨arg, pbody, pcap⟩
          (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l memQt memQt hmem (QTypInQTyp.self memQt))
          (by simp [qtypGuardDesc?, hpredm])))
      simp only [desc, GuardDesc.mk.injEq] at hdesc
      obtain ⟨rfl, rfl, rfl⟩ := hdesc
      have hA := a_in_scope hscope
      obtain ⟨pe1, f', rfl, h1⟩ := equalWithEnvs_body heq
      have hpe1 := equalWithEnvs_v_deref h1
      subst hpe1
      obtain ⟨e1, e2, rfl, he1, he2⟩ := toPExpr?_op hpe
      obtain ⟨e1', rfl, he1'⟩ := toPExpr?_deref he1
      have := toPExpr?_var he1'
      subst this
      obtain ⟨e2', rfl, he2'⟩ := toPExpr?_deref he2
      have := toPExpr?_var he2'
      subst this
      obtain ⟨c1, v1, v2, ht1, ht2, hev, _, _⟩ := terminatesTo_op_inv' _ _ _ _ _ _ hterm
      obtain ⟨c1', a1, m, ht1', hμ1, rfl, hmem1, hvar1, _, _⟩ := terminatesTo_deref_inv' _ _ _ _ ht1
      obtain ⟨vx, hρx, rfl, hvx⟩ := terminatesTo_var_inv' _ _ _ _ ht1'
      subst hvx
      obtain ⟨c2, a0, n, ht2', hμ, rfl, _, _, _, _⟩ := terminatesTo_deref_inv' _ _ _ _ ht2
      obtain ⟨va, hρa, rfl, hva⟩ := terminatesTo_var_inv' _ _ _ _ ht2'
      subst hva
      have hρa' : ρ.lookup "a" = some (Value.loc a0) := by
        rw [hvar1] at hρa; exact hρa
      have hμ' : μ.lookup a0 = some n := by
        rw [hmem1] at hμ; exact hμ
      have hθ := a_at_zero hA hric hρa'
      obtain ⟨w, hw, hty⟩ := hric.2 hlookup
      rw [hρx] at hw
      cases hw
      rw [hetyp] at hty
      cases hty with
      | loc hl1 hin1 =>
        rename_i l1
        obtain ⟨memQt1, hmem1', hpred1⟩ := hall l1 hin1
        refine ⟨Value.num m, Or.inr ⟨x, qt, memQt1, ls, l1, a1, m, "v", body, cap,
          hlookup, hetyp, hin1, hmem1', hpred1, hl1, hμ1, rfl⟩, ?_⟩
        exact cellSat_iff hθ hμ' hev
  · intro k d θ θ' μ μ' v hd hagree
    obtain ⟨rfl, rfl⟩ := tm1_lookup_eq hd
    obtain ⟨d3, hd3⟩ : ∃ deps,
        extractDepsFromPred (Predicate.guardClosure 0 desc.argName desc.body desc.capEnv) 3 =
          .ok deps := ⟨_, rfl⟩
    have h0 : (0 : Loc) ∈ d3 := deps_mem_zero hd3
    obtain ⟨hθ, hμ⟩ := hagree 3 d3 hd3
    have hθ0 := hθ 0 h0
    constructor
    · rintro ⟨-, a, n, m, ha, hn, hv, hlt⟩
      refine ⟨rfl, a, n, m, hθ0 ▸ ha, ?_, hv, hlt⟩
      rw [← hμ 0 h0 a ha]; exact hn
    · rintro ⟨-, a, n, m, ha, hn, hv, hlt⟩
      have ha' : θ.lookup 0 = some a := hθ0 ▸ ha
      refine ⟨rfl, a, n, m, ha', ?_, hv, hlt⟩
      rw [hμ 0 h0 a ha']; exact hn

/-- The law is exercised: in `ctx1` the test `y > !a` selects tag `0`, and
    `match_iff` then says `cellSat` holds in the state where `a` is at address `0`
    (content `0`) and fails where it is at address `1` (content `10`). -/
theorem match_exercised :
    cellSat 0 (θat 0) μ01 (Value.num 5) ∧ ¬ cellSat 0 (θat 1) μ01 (Value.num 5) := by
  obtain ⟨deps, hmatch⟩ := cond_matches
  obtain ⟨v0, hown0, hiff0⟩ :=
    cellSat_lawful.match_iff cond ctx1 10 0 deps μ01 (rho 0) (θat 0) 2 false default
      (cfgOf 0) true ctx1_wf hmatch (ric 0 (by simp [μ01])) cond_runs_0
  obtain ⟨v1, hown1, hiff1⟩ :=
    cellSat_lawful.match_iff cond ctx1 10 0 deps μ01 (rho 1) (θat 1) 2 false default
      (cfgOf 1) false ctx1_wf hmatch (ric 1 (by simp [μ01])) cond_runs_1
  rw [owner_value hown0] at hiff0
  rw [owner_value hown1] at hiff1
  exact ⟨hiff0.mp rfl, fun h => absurd (hiff1.mpr h) (by decide)⟩


/-! ## Guards that `matchGuard` never selects -/

/-- If no context that respects `tm` lets `matchGuard` select a tag, every relation
    meets `match_iff`, and a constant relation meets both laws. -/
theorem constant_lawful_of_never {tm : TagMeaning}
    (hnever : ∀ condition ctx fuel k deps, wfTagMeaningCtx tm ctx →
      matchGuard condition ctx.memEnv ctx.varEnv fuel = .ok (k, deps) → False) :
    PredSatLaws (fun _ _ _ _ => False) tm :=
  ⟨fun condition ctx fuel k deps _ _ _ _ _ _ _ _ hwf hmatch _ _ =>
      (hnever condition ctx fuel k deps hwf hmatch).elim,
    fun _ _ _ _ _ _ _ _ _ => Iff.rfl⟩

/-- The descriptor of the guard closure a successful match selected, from either
    kind of owner. -/
private theorem matched_desc {tm : TagMeaning} {ctx : TypeContext} {condition : Expr} {fuel : Nat}
    {k : Tag} {deps : Deps}
    (hwf : wfTagMeaningCtx tm ctx)
    (hmatch : matchGuard condition ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) :
    ∃ arg pbody pcap, tm.lookup k = some ⟨arg, pbody, pcap⟩ ∧
      GuardInScope ctx.varEnv arg pbody pcap := by
  obtain ⟨_, _, hown⟩ := matchGuard_ok_matched_owner_inScope ctx condition k deps hmatch
  rcases hown with
    ⟨x, qt, arg, pbody, pcap, hlookup, hpred, _, hscope⟩ |
    ⟨x, qt, ls, arg, pbody, pcap, hlookup, _, _, hne, hall, _, hscope⟩
  · exact ⟨arg, pbody, pcap, hwf.1
      (GuardDescInEnvsDeep.intro qt k ⟨arg, pbody, pcap⟩
        (QTypInEnvs.inVar ctx.varEnv ctx.memEnv x qt qt hlookup (QTypInQTyp.self qt))
        (by simp [qtypGuardDesc?, hpred])), hscope⟩
  · obtain ⟨l, hl⟩ : ∃ l, l ∈ ls := by
      have hlist : ls.toList.isEmpty = false := by
        rw [ExtTreeSet.isEmpty_toList]; exact hne
      cases htl : ls.toList with
      | nil => simp [htl] at hlist
      | cons a as => exact ⟨a, ExtTreeSet.mem_toList.mp (by simp [htl])⟩
    obtain ⟨memQt, hmem, hpredm⟩ := hall l hl
    exact ⟨arg, pbody, pcap, hwf.1
      (GuardDescInEnvsDeep.intro memQt k ⟨arg, pbody, pcap⟩
        (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l memQt memQt hmem (QTypInQTyp.self memQt))
        (by simp [qtypGuardDesc?, hpredm])), hscope⟩

namespace TwoTargets

/-- `v => v > !a` with `a : ref {0, 1}`. -/
def cap2 : CapturedVarEnv := [("a", refQt s01)]
def desc2 : GuardDesc := { argName := "v", body := body, capEnv := cap2 }
def tm2 : TagMeaning := (∅ : TagMeaning).update 0 desc2

private theorem s01_toList : s01.toList = [0, 1] := by decide +kernel

/-- No context that respects `tm2` lets `matchGuard` select a guard. -/
theorem never (condition : Expr) (ctx : TypeContext) (fuel : Nat) (k : Tag) (deps : Deps)
    (hwf : wfTagMeaningCtx tm2 ctx)
    (hmatch : matchGuard condition ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) : False := by
  obtain ⟨arg, pbody, pcap, hd, hscope⟩ := matched_desc hwf hmatch
  have hk : k = 0 := by
    by_contra hk
    have hne : ¬ (0 : Tag) = k := fun h => hk h.symm
    simp [tm2, TagMeaning.lookup, TagMeaning.update, hne] at hd
  subst hk
  simp only [tm2, TagMeaning.lookup, TagMeaning.update, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq, desc2, GuardDesc.mk.injEq] at hd
  obtain ⟨rfl, rfl, rfl⟩ := hd
  obtain ⟨qt, ls, l, hcap, _, _, het, hls⟩ := hscope.reads "a" (by simp [PExpr.freeVars, body])
  have : qt = refQt s01 := by
    simpa [cap2, VarTypeEnv.ofCaptured, VarTypeEnv.lookup] using hcap.symm
  subst this
  simp only [refQt, ETyp.ref.injEq] at het
  subst het
  rw [s01_toList] at hls
  simp at hls

theorem lawful : PredSatLaws (fun _ _ _ _ => False) tm2 := constant_lawful_of_never never

end TwoTargets
namespace DerefArg

/-- `v => !v > 0`. -/
def body3 : PExpr := PExpr.op (PExpr.deref (PExpr.var "v")) Op.gt (PExpr.num 0)
def desc3 : GuardDesc := { argName := "v", body := body3, capEnv := [] }
def tm3 : TagMeaning := (∅ : TagMeaning).update 0 desc3

/-- No context that respects `tm3` lets `matchGuard` select a guard. -/
theorem never (condition : Expr) (ctx : TypeContext) (fuel : Nat) (k : Tag) (deps : Deps)
    (hwf : wfTagMeaningCtx tm3 ctx)
    (hmatch : matchGuard condition ctx.memEnv ctx.varEnv fuel = .ok (k, deps)) : False := by
  obtain ⟨arg, pbody, pcap, hd, hscope⟩ := matched_desc hwf hmatch
  have hk : k = 0 := by
    by_contra hk
    have hne : ¬ (0 : Tag) = k := fun h => hk h.symm
    simp [tm3, TagMeaning.lookup, TagMeaning.update, hne] at hd
  subst hk
  simp only [tm3, TagMeaning.lookup, TagMeaning.update, Std.ExtTreeMap.get?_eq_getElem?,
    Std.ExtTreeMap.getElem?_insert_self, Option.some.injEq, desc3, GuardDesc.mk.injEq] at hd
  obtain ⟨rfl, rfl, rfl⟩ := hd
  have h := hscope.noDerefArg
  simp [body3, PExpr.derefsArg, PExpr.usesArg] at h

theorem lawful : PredSatLaws (fun _ _ _ _ => False) tm3 := constant_lawful_of_never never

/-- The dependency set of `v => !v > 0` is empty whenever it is computed. -/
private theorem deps_empty {fuel : Nat} {deps : Deps}
    (h : extractDepsFromPred (Predicate.guardClosure 0 "v" body3 []) fuel = .ok deps) :
    ∀ l, l ∉ deps := by
  rcases fuel with _ | _ | _ | f
  all_goals simp [extractDepsFromPred, extractDepsFromPred.extractDepsFromPExpr, body3] at h
  all_goals simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw, pure,
    Except.pure, bind, Except.bind] at h
  all_goals (subst h; simp [LocSet.union, LocSet.empty])

/-- So the footprint law forces the meaning of tag `0` to depend on the value only:
    consistent, since `match_iff` never constrains it. -/
theorem footprint_forces_constant {predSat : PredSat} (h : PredSatLaws predSat tm3)
    (θ θ' : RealizationMap) (μ μ' : Memory) (v : Value) :
    predSat 0 θ μ v ↔ predSat 0 θ' μ' v :=
  h.mem_footprint 0 desc3 θ θ' μ μ' v (by simp [tm3, TagMeaning.lookup, TagMeaning.update])
    (fun _ _ hdeps => ⟨fun l hl => (deps_empty hdeps l hl).elim,
      fun l hl => (deps_empty hdeps l hl).elim⟩)

end DerefArg

end PredSatLawsCellWitness
