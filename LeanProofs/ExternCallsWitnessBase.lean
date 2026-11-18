import LeanProofs.PredSatLawsWitness
import LeanProofs.ExternCallSteps

/-!
# Premises on extern calls for concrete programs: shared pieces

The fault-robustness theorem takes three premises on extern calls:
`ExternCallsMatch` for each run and `ExternCallsAgree` for the pair. The
module `ExternCallsWitness` proves and refutes them for small programs that
call a pure extern `read`, the identity on integers, whose result carries the
guard `w => w >= 0`. This module holds the pieces those proofs share:

* `terminatesTo` is deterministic (`terminatesTo_det`);
* the laws fix `predSat` at a `w => w >= 0` guard (`pin_ge`), and the relation
  `geSat` is lawful for every table of such guards (`predSatLaws_geSat`);
* inversion of `SubStep` and `ExternCallAt` at `let`, `if` and application
  steps, and the fact that no step below an expression without applications
  calls an extern (`ExternCallAt.not_of_reach_noApp`);
* the registry and the declaration of `read`, the run of a call of `read`, and
  the parts and the extern call of that step.

Imported by `ExternCallsWitness` and `ExternCallsWitnessCell` (which reuses
the general pieces for a call of an extern function); not on the proof path
of the theorem.
-/

open Std LeanPoison

namespace ExternCallsWitness

/-! ## `terminatesTo` is deterministic -/

/-- A successful evaluation keeps its result with more fuel and either value of
    `verbose`. -/
private theorem beval_mono :
    ∀ (n : Nat) (c : Config) (e : Expr) (vb : Bool) (c' : Config) (v : Value),
    beval n c e vb = .success c' v →
    ∀ (m : Nat) (vb' : Bool), n ≤ m → beval m c e vb' = .success c' v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro c e vb c' v h m vb' hle
  rcases n with _ | n
  · unfold beval at h; simp at h
  rcases m with _ | m
  · omega
  have lift : ∀ {c e c' v}, beval n c e vb = .success c' v → beval m c e vb' = .success c' v :=
    fun h => IH n (by omega) _ _ vb _ _ h m vb' (by omega)
  have liftB : ∀ {cur env x arg body pure c' v},
      bevalFunctionBody n vb cur env x arg body pure = .success c' v →
      bevalFunctionBody m vb' cur env x arg body pure = .success c' v := by
    intro cur env x arg body pure c' v hb
    rcases n with _ | n
    · simp [bevalFunctionBody] at hb
    rcases m with _ | m
    · omega
    simp only [bevalFunctionBody] at hb ⊢
    cases hx : beval n { cur with varEnv := VarEnv.update env x arg, pureMode := pure } body vb with
    | success c1 v1 =>
        rw [hx] at hb
        rw [IH n (by omega) _ _ vb _ _ hx m vb' (by omega)]
        (try simp only at hb ⊢)
        exact hb
    | outOfFuel => rw [hx] at hb; simp at hb
    | runtimeError _ => rw [hx] at hb; simp at hb
  cases e <;>
    (unfold beval at h ⊢
     try simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at h ⊢)
  all_goals try exact h
  case op e1 o e2 =>
      cases h1 : beval n c e1 vb with
      | success c1 v1 =>
          rw [h1] at h; rw [lift h1]; (try simp only at h ⊢)
          cases h2 : beval n c1 e2 vb with
          | success c2 v2 => rw [h2] at h; rw [lift h2]; (try simp only at h ⊢); exact h
          | outOfFuel => rw [h2] at h; simp at h
          | runtimeError _ => rw [h2] at h; simp at h
      | outOfFuel => rw [h1] at h; simp at h
      | runtimeError _ => rw [h1] at h; simp at h
  case unaryop o e1 =>
      cases h1 : beval n c e1 vb with
      | success c1 v1 => rw [h1] at h; rw [lift h1]; (try simp only at h ⊢); exact h
      | outOfFuel => rw [h1] at h; simp at h
      | runtimeError _ => rw [h1] at h; simp at h
  case newRef e1 =>
      split at h
      · simp at h
      · rename_i hpm
        simp only [hpm, Bool.false_eq_true, ↓reduceIte]
        cases h1 : beval n c e1 vb with
        | success c1 v1 => rw [h1] at h; rw [lift h1]; exact h
        | outOfFuel => rw [h1] at h; simp at h
        | runtimeError _ => rw [h1] at h; simp at h
  case deref e1 =>
      cases h1 : beval n c e1 vb with
      | success c1 v1 => rw [h1] at h; rw [lift h1]; exact h
      | outOfFuel => rw [h1] at h; simp at h
      | runtimeError _ => rw [h1] at h; simp at h
  case assign e1 e2 =>
      split at h
      · simp at h
      · rename_i hpm
        simp only [hpm, Bool.false_eq_true, ↓reduceIte]
        cases h1 : beval n c e1 vb with
        | success c1 v1 =>
            rw [h1] at h; rw [lift h1]
            cases v1 with
            | loc l =>
                simp only at h ⊢
                cases h2 : beval n c1 e2 vb with
                | success c2 v2 => rw [h2] at h; rw [lift h2]; exact h
                | outOfFuel => rw [h2] at h; simp at h
                | runtimeError _ => rw [h2] at h; simp at h
            | _ => simp at h
        | outOfFuel => rw [h1] at h; simp at h
        | runtimeError _ => rw [h1] at h; simp at h
  case seq e1 e2 =>
      cases h1 : beval n c e1 vb with
      | success c1 v1 =>
          rw [h1] at h; rw [lift h1]; (try simp only at h ⊢)
          cases h2 : beval n c1 e2 vb with
          | success c2 v2 => rw [h2] at h; rw [lift h2]; (try simp only at h ⊢); exact h
          | outOfFuel => rw [h2] at h; simp at h
          | runtimeError _ => rw [h2] at h; simp at h
      | outOfFuel => rw [h1] at h; simp at h
      | runtimeError _ => rw [h1] at h; simp at h
  case ite e1 e2 e3 =>
      cases h1 : beval n c e1 vb with
      | success c1 v1 =>
          rw [h1] at h; rw [lift h1]
          cases v1 with
          | bool b =>
              cases b with
              | true =>
                  simp only at h ⊢
                  cases h2 : beval n c1 e2 vb with
                  | success c2 v2 => rw [h2] at h; rw [lift h2]; (try simp only at h ⊢); exact h
                  | outOfFuel => rw [h2] at h; simp at h
                  | runtimeError _ => rw [h2] at h; simp at h
              | false =>
                  simp only at h ⊢
                  cases h2 : beval n c1 e3 vb with
                  | success c2 v2 => rw [h2] at h; rw [lift h2]; (try simp only at h ⊢); exact h
                  | outOfFuel => rw [h2] at h; simp at h
                  | runtimeError _ => rw [h2] at h; simp at h
          | _ => simp at h
      | outOfFuel => rw [h1] at h; simp at h
      | runtimeError _ => rw [h1] at h; simp at h
  case vlet x e1 e2 =>
      cases h1 : beval n c e1 vb with
      | success c1 v1 =>
          rw [h1] at h; rw [lift h1]; (try simp only at h ⊢)
          cases h2 : beval n { c1 with varEnv := c.varEnv.update x v1 } e2 vb with
          | success c2 v2 => rw [h2] at h; rw [lift h2]; (try simp only at h ⊢); exact h
          | outOfFuel => rw [h2] at h; simp at h
          | runtimeError _ => rw [h2] at h; simp at h
      | outOfFuel => rw [h1] at h; simp at h
      | runtimeError _ => rw [h1] at h; simp at h
  case app e1 e2 =>
      cases h2 : beval n c e2 vb with
      | success c2 v2 =>
          rw [h2] at h; rw [lift h2]; (try simp only at h ⊢)
          cases h1 : beval n { c2 with varEnv := c.varEnv } e1 vb with
          | success c1 v1 =>
              rw [h1] at h; rw [lift h1]
              cases v1 with
              | closure x body env =>
                  simp only at h ⊢
                  cases body with
                  | externFn _ _ _ _ _ _ _ _ => exact h
                  | _ =>
                      simp only at h ⊢
                      split at h
                      · simp at h
                      · rename_i hpm
                        split
                        · contradiction
                        · exact liftB h
              | peClosure x body env =>
                  simp only at h ⊢
                  cases body with
                  | externPfn _ _ _ _ _ _ _ => exact h
                  | _ =>
                      simp only at h ⊢
                      split at h
                      · rename_i hp
                        exact liftB h
                      · simp at h
              | _ => simp at h
          | outOfFuel => rw [h1] at h; simp at h
          | runtimeError _ => rw [h1] at h; simp at h
      | outOfFuel => rw [h2] at h; simp at h
      | runtimeError _ => rw [h2] at h; simp at h

/-- `terminatesTo` is deterministic. -/
theorem terminatesTo_det {e : Expr} {c c₁ c₂ : Config} {v₁ v₂ : Value}
    (h₁ : terminatesTo e c c₁ v₁) (h₂ : terminatesTo e c c₂ v₂) : c₁ = c₂ ∧ v₁ = v₂ := by
  obtain ⟨n₁, vb₁, h₁⟩ := h₁
  obtain ⟨n₂, vb₂, h₂⟩ := h₂
  have e₁ := beval_mono n₁ c e vb₁ c₁ v₁ h₁ (max n₁ n₂) false (le_max_left _ _)
  have e₂ := beval_mono n₂ c e vb₂ c₂ v₂ h₂ (max n₁ n₂) false (le_max_right _ _)
  rw [e₁] at e₂
  cases e₂
  exact ⟨rfl, rfl⟩

/-! ## The guard `a => a >= 0` -/

/-- The body `a >= 0`. -/
def geBody (a : Name) : PExpr := PExpr.op (PExpr.var a) Op.gte (PExpr.num 0)

/-- Every guard of the table is `a => a >= 0` for its own argument name `a`. -/
def GeTable (P : TagMeaning) : Prop :=
  ∀ k d, P.lookup k = some d → d.body = geBody d.argName

/-- The checked value is a non-negative integer. -/
def geSat : PredSat := fun _ _ _ v => ∃ n : Int, v = Value.num n ∧ 0 ≤ n

private theorem eq_num {n : Int} {p : PExpr} {cap sCap : CapturedVarEnv}
    {subst : Option (Name × PExpr)} {fuel : Nat}
    (h : PExpr.equalWithEnvs (PExpr.num n) cap p sCap subst fuel = true) :
    p = PExpr.num n := by
  cases fuel with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ fuel => cases p <;> simp_all [PExpr.equalWithEnvs]

/-- The argument replaced by a variable `x` matches only `x`. -/
private theorem eq_var_arg {a x : Name} {p : PExpr} {cap sCap : CapturedVarEnv} {fuel : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var a) cap p sCap (some (a, PExpr.var x)) fuel = true) :
    p = PExpr.var x := by
  cases fuel with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ fuel =>
      by_cases hx : x = a
      · subst hx
        cases p <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
      · have hbeq : (PExpr.var x == PExpr.var a) = false := by
          simp [BEq.beq, beqPExpr, hx]
        cases fuel with
        | zero => simp [PExpr.equalWithEnvs, hbeq] at h
        | succ fuel =>
            cases p <;> simp_all [PExpr.equalWithEnvs]

/-- With the argument replaced by `!a` itself, the substitution never ends. -/
private theorem eq_deref_self_false {a : Name} {cap sCap : CapturedVarEnv} :
    ∀ (fuel : Nat) (p : PExpr),
      PExpr.equalWithEnvs (PExpr.var a) cap p sCap
        (some (a, PExpr.deref (PExpr.var a))) fuel = false := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
      intro p
      have hbeq : (PExpr.deref (PExpr.var a) == PExpr.var a) = false := by
        simp [BEq.beq, beqPExpr]
      match fuel with
      | 0 => simp [PExpr.equalWithEnvs]
      | 1 => simp [PExpr.equalWithEnvs, hbeq]
      | f + 2 =>
          cases p with
          | deref p' =>
              simp only [PExpr.equalWithEnvs, beq_self_eq_true, ite_true, hbeq,
                Bool.false_eq_true, ite_false]
              exact ih f (by omega) p'
          | _ => simp [PExpr.equalWithEnvs, hbeq]

/-- The argument replaced by `!x` matches only `!x`, and only when `x` is not `a`. -/
private theorem eq_deref_arg {a x : Name} {p : PExpr} {cap sCap : CapturedVarEnv} {fuel : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var a) cap p sCap
      (some (a, PExpr.deref (PExpr.var x))) fuel = true) :
    p = PExpr.deref (PExpr.var x) := by
  by_cases hx : x = a
  · subst hx
    rw [eq_deref_self_false fuel p] at h
    cases h
  · have hbeq : (PExpr.deref (PExpr.var x) == PExpr.var a) = false := by
      simp [BEq.beq, beqPExpr]
    match fuel with
    | 0 => simp [PExpr.equalWithEnvs] at h
    | 1 => simp [PExpr.equalWithEnvs, hbeq] at h
    | f + 2 =>
        cases p with
        | deref p' =>
            simp only [PExpr.equalWithEnvs, beq_self_eq_true, ite_true, hbeq,
              Bool.false_eq_true, ite_false] at h
            have hxa : (x == a) = false := by simp [hx]
            cases f with
            | zero => simp [PExpr.equalWithEnvs] at h
            | succ f =>
                cases p' <;> simp_all [PExpr.equalWithEnvs]
        | _ => simp [PExpr.equalWithEnvs, hbeq] at h

/-- The body `a >= 0` with the argument replaced by `arg` matches `arg >= 0`. -/
private theorem eq_geBody {a : Name} {arg p : PExpr} {cap sCap : CapturedVarEnv}
    {fuel : Nat}
    (h : PExpr.equalWithEnvs (geBody a) cap p sCap (some (a, arg)) fuel = true) :
    ∃ p1, p = PExpr.op p1 Op.gte (PExpr.num 0) ∧
      ∃ f, PExpr.equalWithEnvs (PExpr.var a) cap p1 sCap (some (a, arg)) f = true := by
  cases fuel with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ fuel =>
      cases p with
      | op p1 o p2 =>
          simp only [geBody, PExpr.equalWithEnvs, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨ho, h1⟩, h2⟩ := h
          subst ho
          rw [eq_num h2]
          exact ⟨p1, rfl, fuel, h1⟩
      | _ => simp [geBody, PExpr.equalWithEnvs] at h

private theorem toPExpr?_var {e : Expr} {x : Name}
    (h : e.toPExpr? = some (PExpr.var x)) : e = Expr.var x := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_num {e : Expr} {n : Int}
    (h : e.toPExpr? = some (PExpr.num n)) : e = Expr.num n := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_deref {e : Expr} {pe : PExpr}
    (h : e.toPExpr? = some (PExpr.deref pe)) :
    ∃ e', e = Expr.deref e' ∧ e'.toPExpr? = some pe := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_deref_var {e : Expr} {x : Name}
    (h : e.toPExpr? = some (PExpr.deref (PExpr.var x))) :
    e = Expr.deref (Expr.var x) := by
  obtain ⟨e', rfl, he'⟩ := toPExpr?_deref h
  rw [toPExpr?_var he']

private theorem toPExpr?_op {e : Expr} {p1 p2 : PExpr} {o : Op}
    (h : e.toPExpr? = some (PExpr.op p1 o p2)) :
    ∃ e1 e2, e = Expr.op e1 o e2 ∧ e1.toPExpr? = some p1 ∧ e2.toPExpr? = some p2 := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_ge {e : Expr} {p1 : PExpr}
    (h : e.toPExpr? = some (PExpr.op p1 Op.gte (PExpr.num 0))) :
    ∃ e1, e = Expr.op e1 Op.gte (Expr.num 0) ∧ e1.toPExpr? = some p1 := by
  obtain ⟨e1, e2, rfl, h1, h2⟩ := toPExpr?_op h
  rw [toPExpr?_num h2]
  exact ⟨e1, rfl, h1⟩

private theorem eval_ge {e1 : Expr} {cfg cfg' : Config} {b : Bool}
    (h : terminatesTo (Expr.op e1 Op.gte (Expr.num 0)) cfg cfg' (Value.bool b)) :
    ∃ c₁ n, terminatesTo e1 cfg c₁ (Value.num n) ∧ (b = true ↔ 0 ≤ n) := by
  obtain ⟨c₁, v₁, v₂, h1, h2, hop, _, _⟩ := terminatesTo_op_inv' _ _ _ _ _ _ h
  obtain ⟨-, rfl⟩ := terminatesTo_literal_inv' (Expr.num 0) (Value.num 0) rfl _ _ _ h2
  cases v₁ with
  | num n =>
      simp only [evalOp, Option.some.injEq, Value.bool.injEq] at hop
      refine ⟨c₁, n, h1, ?_⟩
      rw [← hop]
      simp
  | _ => simp [evalOp] at hop

private theorem desc_of_lookup {P : TagMeaning} {ctx : TypeContext} {k : Tag}
    {qt : QTyp} {arg : Name} {body : PExpr} {cap : CapturedVarEnv}
    (hwf : wfTagMeaningCtx P ctx) (hin : QTypInEnvs qt ctx.varEnv ctx.memEnv)
    (hpred : qt.pred = Predicate.guardClosure k arg body cap) :
    P.lookup k = some ⟨arg, body, cap⟩ :=
  hwf.1 (GuardDescInEnvsDeep.intro qt k ⟨arg, body, cap⟩ hin
    (by simp [qtypGuardDesc?, hpred]))

/-- `geSat` is lawful for every table of `a => a >= 0` guards. -/
theorem predSatLaws_geSat {P : TagMeaning} (hP : GeTable P) : PredSatLaws geSat P := by
  refine ⟨?_, ?_⟩
  · intro condition ctx fuel k deps μ ρ θ addr pm registry cfg b hwf hmatch hric hterm
    obtain ⟨pe, hpe, hown⟩ := matchGuard_ok_matched_owner ctx condition k deps hmatch
    rcases hown with
      ⟨x, qt, arg, body, cap, hlookup, hpred, heq⟩ |
      ⟨x, qt, ls, arg, body, cap, hlookup, hetyp, hne, hall, heq⟩
    · -- The owner is the variable `x`.
      have hdesc := desc_of_lookup hwf
        (QTypInEnvs.inVar ctx.varEnv ctx.memEnv x qt qt hlookup (QTypInQTyp.self qt)) hpred
      have hbody : body = geBody arg := hP k _ hdesc
      subst hbody
      obtain ⟨p1, rfl, f, h1⟩ := eq_geBody heq
      have hp1 : p1 = PExpr.var x := eq_var_arg h1
      subst hp1
      obtain ⟨e1, rfl, he1⟩ := toPExpr?_ge hpe
      have he1' : e1 = Expr.var x := toPExpr?_var he1
      subst he1'
      obtain ⟨c₁, n, hx, hb⟩ := eval_ge hterm
      obtain ⟨v', hρ, -, hv⟩ := terminatesTo_var_inv' x _ _ _ hx
      subst hv
      refine ⟨Value.num n, Or.inl ⟨x, qt, arg, geBody arg, cap, hlookup, hpred, hρ⟩, ?_⟩
      rw [hb]
      simp [geSat]
    · -- The owner is a cell that the reference `x` points to.
      obtain ⟨l, hl⟩ : ∃ l, l ∈ ls := by
        have hlist : ls.toList.isEmpty = false := by
          rw [ExtTreeSet.isEmpty_toList]; exact hne
        cases htl : ls.toList with
        | nil => simp [htl] at hlist
        | cons a as => exact ⟨a, ExtTreeSet.mem_toList.mp (by simp [htl])⟩
      obtain ⟨memQt, hmem, hpred⟩ := hall l hl
      have hdesc := desc_of_lookup hwf
        (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l memQt memQt hmem (QTypInQTyp.self memQt)) hpred
      have hbody : body = geBody arg := hP k _ hdesc
      subst hbody
      obtain ⟨p1, rfl, f, h1⟩ := eq_geBody heq
      have hp1 : p1 = PExpr.deref (PExpr.var x) := eq_deref_arg h1
      subst hp1
      obtain ⟨e1, rfl, he1⟩ := toPExpr?_ge hpe
      have he1' : e1 = Expr.deref (Expr.var x) := toPExpr?_deref_var he1
      subst he1'
      obtain ⟨c₁, n, hx, hb⟩ := eval_ge hterm
      obtain ⟨c₁', a, n', hloc, hcell, hv, -⟩ := terminatesTo_deref_inv' _ _ _ _ hx
      obtain ⟨v', hρ, hc, hv'⟩ := terminatesTo_var_inv' x _ _ _ hloc
      subst hc
      cases hv
      -- `x` holds the address `a`; the typing of `x` gives the logical location.
      obtain ⟨v'', hρ', hvt⟩ := hric.2 hlookup
      rw [hρ] at hρ'
      cases hρ'
      rw [hetyp, ← hv'] at hvt
      cases hvt with
      | loc hθ hin =>
          rename_i l0
          obtain ⟨memQt0, hmem0, hpred0⟩ := hall l0 hin
          refine ⟨Value.num n,
            Or.inr ⟨x, qt, memQt0, ls, l0, a, n, arg, geBody arg, cap, hlookup, hetyp, hin,
              hmem0, hpred0, hθ, hcell, rfl⟩, ?_⟩
          rw [hb]
          simp [geSat]
  · intro _ _ _ _ _ _ _ _ _
    exact Iff.rfl

/-! ### The laws fix `predSat` at a `w => w >= 0` guard

The proof applies the law `match_iff` to a context built for the purpose: one
variable `y` that carries the guard, and the test `y >= 0`. -/

private def pinQt (k : Tag) (cap : CapturedVarEnv) : QTyp :=
  { etyp := ETyp.int, poison := true, pred := Predicate.guardClosure k "w" (geBody "w") cap }

private def pinCtx (k : Tag) (cap : CapturedVarEnv) : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅,
    varEnv := (∅ : VarTypeEnv).update "y" (pinQt k cap), tagEnv := ∅,
    nextLoc := 0, nextTag := k + 1, pureCtx := false }

private theorem pinCtx_lookup {k : Tag} {cap : CapturedVarEnv} {x : Name} {qt : QTyp}
    (h : (pinCtx k cap).varEnv.lookup x = some qt) : x = "y" ∧ qt = pinQt k cap := by
  simp only [pinCtx] at h
  by_cases hy : x = "y"
  · subst hy
    rw [VarTypeEnv_lookup_update_eq] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩
  · rw [VarTypeEnv_lookup_update_ne _ "y" x _ hy] at h
    simp [VarTypeEnv.lookup] at h

private theorem pinCtx_wf {P : TagMeaning} {k : Tag} {cap : CapturedVarEnv}
    (hP : P.lookup k = some { argName := "w", body := geBody "w", capEnv := cap }) :
    wfTagMeaningCtx P (pinCtx k cap) := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k' d hdeep
  rcases hdeep with ⟨qt, k', d, hin, hdesc⟩
  cases hin with
  | inVar _ _ x _ qtRoot hlookup hinq =>
    obtain ⟨_, rfl⟩ := pinCtx_lookup hlookup
    have hqt : qt = pinQt k cap :=
      QTypInQTyp_eq_of_nonFunctionTarget hinq
        (by simp [pinQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
    subst hqt
    simp [qtypGuardDesc?, pinQt] at hdesc
    obtain ⟨rfl, rfl⟩ := hdesc
    exact hP
  | inMem _ _ l _ qtRoot hlookup hinq =>
    simp [pinCtx, MemoryTypeEnv.lookup] at hlookup

private def pinRho (n : Int) : VarEnv := [("y", Value.num n)]

private def pinCfg (μ : Memory) (n : Int) : Config :=
  { memory := μ, varEnv := pinRho n, nextAddr := 0, pureMode := false, registry := default }

private theorem pinRic (k : Tag) (cap : CapturedVarEnv) (μ : Memory) (n : Int) :
    runtimeInstantiatesCtx (pinCtx k cap) μ (pinRho n) (∅ : RealizationMap) := by
  refine ⟨?_, ?_⟩
  · intro l a h
    simp [RealizationMap.lookup] at h
  · intro x qt h
    obtain ⟨rfl, rfl⟩ := pinCtx_lookup h
    exact ⟨Value.num n, rfl, valueHasETyp.num _⟩

private def pinCond : Expr := Expr.op (Expr.var "y") Op.gte (Expr.num 0)

private theorem pinCond_matches (k : Tag) (cap : CapturedVarEnv) :
    ∃ deps, matchGuard pinCond (pinCtx k cap).memEnv (pinCtx k cap).varEnv 10 = .ok (k, deps) :=
  ⟨_, rfl⟩

private theorem pinCond_runs (μ : Memory) (n : Int) :
    terminatesTo pinCond (pinCfg μ n) (pinCfg μ n) (Value.bool (decide (n ≥ 0))) := by
  refine ⟨2, false, ?_⟩
  have hy : VarEnv.lookup (pinRho n) "y" = some (Value.num n) := rfl
  simp [pinCond, LeanPoison.beval, LeanPoison.evalOp, pinCfg, hy]

/-- The guard closure `w => w >= 0` reads no location: every set that the extraction
    computes for it is empty. -/
private theorem ge_deps_empty {k : Tag} {cap : CapturedVarEnv} {fuel : Nat} {deps : Deps}
    (h : extractDepsFromPred (Predicate.guardClosure k "w" (geBody "w") cap) fuel = .ok deps) :
    ∀ l, l ∉ deps := by
  intro l hl
  unfold extractDepsFromPred at h
  rcases fuel with _ | _ | f
  · simp [extractDepsFromPred.extractDepsFromPExpr] at h
  · simp [extractDepsFromPred.extractDepsFromPExpr, geBody, throw, throwThe,
      MonadExceptOf.throw, Except.bind, Bind.bind] at h
  · simp [extractDepsFromPred.extractDepsFromPExpr, geBody, Pure.pure, Except.pure,
      Except.bind, Bind.bind] at h
    subst h
    simp [LocSet.union, LocSet.empty, ExtTreeSet.mem_union_iff] at hl

/-- The laws fix `predSat` at a tag whose guard is `w => w >= 0`: on an integer
    `n` it holds exactly when `0 ≤ n`, under every realisation map and memory.
    The table, the tag and the captured environment of the guard are
    arbitrary. -/
theorem pin_ge (predSat : PredSat) (P : TagMeaning) (k : Tag) (cap : CapturedVarEnv)
    (hlaws : PredSatLaws predSat P)
    (hP : P.lookup k = some { argName := "w", body := geBody "w", capEnv := cap })
    (θ : RealizationMap) (μ : Memory) (n : Int) :
    predSat k θ μ (Value.num n) ↔ 0 ≤ n := by
  have h0 : predSat k ∅ μ (Value.num n) ↔ 0 ≤ n := by
    obtain ⟨deps, hmatch⟩ := pinCond_matches k cap
    obtain ⟨v, hown, hiff⟩ :=
      hlaws.match_iff pinCond (pinCtx k cap) 10 k deps μ (pinRho n) ∅ 0 false default
        (pinCfg μ n) (decide (n ≥ 0)) (pinCtx_wf hP) hmatch (pinRic k cap μ n) (pinCond_runs μ n)
    have hv : v = Value.num n := by
      rcases hown with ⟨x, qt, _, _, _, hlookup, hpred, hρ⟩ |
        ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hmem, _⟩
      · obtain ⟨rfl, rfl⟩ := pinCtx_lookup hlookup
        have hl : (pinRho n).lookup "y" = some (Value.num n) := rfl
        rw [hl] at hρ
        exact (Option.some.inj hρ).symm
      · simp [pinCtx, MemoryTypeEnv.lookup] at hmem
    rw [hv] at hiff
    rw [← hiff]
    simp
  rw [← h0]
  exact hlaws.mem_footprint k _ θ ∅ μ μ (Value.num n) hP
    (fun _ _ hdeps => ⟨fun l hl => absurd hl (ge_deps_empty hdeps l),
      fun l hl => absurd hl (ge_deps_empty hdeps l)⟩)

/-- The descriptor at `k` is `w => w >= 0`. -/
def descGe (P : TagMeaning) (k : Tag) : Bool :=
  match P.lookup k with
  | some d => d.argName == "w" && d.body == geBody "w"
  | none => false

theorem descGe_spec {P : TagMeaning} {k : Tag} (h : descGe P k = true) :
    ∃ cap, P.lookup k = some { argName := "w", body := geBody "w", capEnv := cap } := by
  unfold descGe at h
  cases hk : P.lookup k with
  | none => rw [hk] at h; simp at h
  | some d =>
      rw [hk] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      cases d
      simp only at h1 h2
      subst h1 h2
      exact ⟨_, rfl⟩

/-- The predicate of a lawful `predSat` at a `w => w >= 0` tag. -/
theorem pin {predSat : PredSat} {P : TagMeaning} {k : Tag} (hlaws : PredSatLaws predSat P)
    (hd : descGe P k = true) (θ : RealizationMap) (μ : Memory) (n : Int) :
    predSat k θ μ (.num n) ↔ 0 ≤ n := by
  obtain ⟨cap, hP⟩ := descGe_spec hd
  exact pin_ge predSat P k cap hlaws hP θ μ n

/-- Every descriptor of the log is `a => a >= 0`. -/
def allGe (log : List TagAlloc) : Bool :=
  log.all fun a => a.body == geBody a.argName

theorem geTable_of_allGe {log : List TagAlloc} (h : allGe log = true) :
    GeTable (programTable ∅ log) := by
  intro k d hk
  rcases programTable_within ∅ log k d hk with h0 | ⟨a, ha, _, rfl⟩
  · simp [TagMeaning.lookup] at h0
  · simp only [allGe, List.all_eq_true, beq_iff_eq] at h
    exact h a ha

/-! ## Typing results -/

/-- The result of a typing run that succeeds; a fixed value otherwise. -/
def okVal (x : TypecheckM TypeResult) : TypeResult :=
  match x with
  | .ok r => r
  | .error _ => { qualType := ⟨.int, false, .noPred⟩, memEnv' := ∅, tagEnv' := ∅,
                  nextLoc' := 0, nextTag' := 0, regime' := ∅, declared' := [] }

def isOkB (x : TypecheckM TypeResult) : Bool :=
  match x with
  | .ok _ => true
  | .error _ => false

theorem eq_okVal {x : TypecheckM TypeResult} (h : isOkB x = true) : x = .ok (okVal x) := by
  cases x <;> simp_all [isOkB, okVal]

theorem ok_inj {x : TypecheckM TypeResult} {a b : TypeResult} (ha : x = .ok a)
    (hb : x = .ok b) : a = b := by
  rw [ha] at hb; cases hb; rfl

theorem okVal_of_eq {x : TypecheckM TypeResult} {r : TypeResult} (h : x = .ok r) :
    okVal x = r := by
  rw [h]; rfl

/-! ## Inversion of steps and calls -/

theorem SubStep.vlet_inv {ctx : TypeContext} {x : Name} {e1 e2 : Expr} {F : Nat} {cfg : Config}
    {s' : Step} (h : SubStep ⟨ctx, .vlet x e1 e2, F, cfg⟩ s') :
    ∃ f, F = f + 2 ∧
      (s' = ⟨ctx, e1, f, cfg⟩ ∨
       ∃ r1 c1 v1, typecheckExpr ctx e1 f = .ok r1 ∧ terminatesTo e1 cfg c1 v1 ∧
         s' = ⟨{ ctxAfter ctx r1 with varEnv := ctx.varEnv.update x r1.qualType }, e2, f,
               { c1 with varEnv := cfg.varEnv.update x v1 }⟩) := by
  cases h with
  | vletBound => exact ⟨_, rfl, Or.inl rfl⟩
  | vletBody h1 h2 => exact ⟨_, rfl, Or.inr ⟨_, _, _, h1, h2, rfl⟩⟩

/-- The parts of an `if` step, by arm of `typecheckIf`. -/
theorem SubStep.ite_inv {ctx : TypeContext} {e1 e2 e3 : Expr} {F : Nat} {cfg : Config}
    {s' : Step} (h : SubStep ⟨ctx, .ite e1 e2 e3, F, cfg⟩ s') :
    ∃ f, F = f + 2 ∧
      ((∃ k deps b, matchGuard e1 ctx.memEnv ctx.varEnv f = .ok (k, deps) ∧
          ctx.regime.lookup? k = some b ∧ s' = ⟨{ ctx with pureCtx := true }, e1, f, cfg⟩) ∨
       (∃ k deps b r1 c1, matchGuard e1 ctx.memEnv ctx.varEnv f = .ok (k, deps) ∧
          ctx.regime.lookup? k = some b ∧
          typecheckExpr { ctx with pureCtx := true } e1 f = .ok r1 ∧
          terminatesTo e1 cfg c1 (.bool true) ∧ s' = ⟨ctxTrue ctx k deps r1, e2, f, c1⟩) ∨
       (∃ k deps b r1 r2 c1, matchGuard e1 ctx.memEnv ctx.varEnv f = .ok (k, deps) ∧
          ctx.regime.lookup? k = some b ∧
          typecheckExpr { ctx with pureCtx := true } e1 f = .ok r1 ∧
          terminatesTo e1 cfg c1 (.bool false) ∧
          typecheckExpr (ctxTrue ctx k deps r1) e2 f = .ok r2 ∧
          s' = ⟨ctxFalse' ctx k deps r2, e3, f, c1⟩) ∨
       (StdArm ctx e1 f ∧ s' = ⟨ctx, e1, f, cfg⟩) ∨
       (∃ r1 c1, StdArm ctx e1 f ∧ typecheckExpr ctx e1 f = .ok r1 ∧
          terminatesTo e1 cfg c1 (.bool true) ∧ s' = ⟨ctxStd ctx r1, e2, f, c1⟩) ∨
       (∃ r1 r2 c1, StdArm ctx e1 f ∧ typecheckExpr ctx e1 f = .ok r1 ∧
          terminatesTo e1 cfg c1 (.bool false) ∧ typecheckExpr (ctxStd ctx r1) e2 f = .ok r2 ∧
          s' = ⟨ctxStdElse ctx r1 r2, e3, f, c1⟩)) := by
  cases h with
  | iteCondPure h1 h2 => exact ⟨_, rfl, Or.inl ⟨_, _, _, h1, h2, rfl⟩⟩
  | iteThenMatched h1 h2 h3 h4 =>
      exact ⟨_, rfl, Or.inr (Or.inl ⟨_, _, _, _, _, h1, h2, h3, h4, rfl⟩)⟩
  | iteElseMatched h1 h2 h3 h4 h5 =>
      exact ⟨_, rfl, Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, h1, h2, h3, h4, h5, rfl⟩))⟩
  | iteCondStd h1 => exact ⟨_, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, rfl⟩)))⟩
  | iteThenStd h1 h2 h3 =>
      exact ⟨_, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, h1, h2, h3, rfl⟩))))⟩
  | iteElseStd h1 h2 h3 h4 =>
      exact ⟨_, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, h1, h2, h3, h4, rfl⟩))))⟩

/-- The parts of an application step. `G` is the fuel of the argument and the
    function; a body is typed at `G - 1`. -/
theorem SubStep.app_inv {ctx : TypeContext} {e1 e2 : Expr} {F : Nat} {cfg : Config}
    {s' : Step} (h : SubStep ⟨ctx, .app e1 e2, F, cfg⟩ s') :
    ∃ G, F = G + 2 ∧
      (s' = ⟨ctx, e2, G, cfg⟩ ∨
       (∃ r2 c2 v2, typecheckExpr ctx e2 G = .ok r2 ∧ terminatesTo e2 cfg c2 v2 ∧
         s' = ⟨ctxAfter ctx r2, e1, G, { c2 with varEnv := cfg.varEnv }⟩) ∨
       (∃ H r2 r1 rb c2 c1 v2 x body env st1 st2 p tcls tenv cursor, G = H + 1 ∧
         typecheckExpr ctx e2 G = .ok r2 ∧ terminatesTo e2 cfg c2 v2 ∧
         typecheckExpr (ctxAfter ctx r2) e1 G = .ok r1 ∧
         terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1 (.closure x body env) ∧
         r1.qualType.etyp = .arrow st1 st2 p tcls ∧
         ThreadedAt (fnApply ctx r2 r1 st1 st2 p G) tcls (r1.nextTag', r1.nextLoc')
           (.regular x body tenv) cursor rb ∧
         s' = ⟨fnBodyCtx ctx r2 r1 p x tenv cursor, body, H,
               { c1 with varEnv := VarEnv.update env x v2, pureMode := false }⟩) ∨
       (∃ H r2 r1 rb c2 c1 v2 x body pbody env st1 st2 p tcls tenv cursor, G = H + 1 ∧
         typecheckExpr ctx e2 G = .ok r2 ∧ terminatesTo e2 cfg c2 v2 ∧
         typecheckExpr (ctxAfter ctx r2) e1 G = .ok r1 ∧
         terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1 (.peClosure x body env) ∧
         r1.qualType.etyp = .parrow st1 st2 p tcls ∧
         Expr.toPExpr? body = some pbody ∧
         ThreadedAt (pfnApply ctx r2 r1 st1 st2 p G) tcls (r1.nextTag', r1.nextLoc')
           (.regular x pbody tenv) cursor rb ∧
         s' = ⟨pfnBodyCtx ctx r2 r1 p x tenv cursor, PExpr.toExpr pbody, H,
               { c1 with varEnv := VarEnv.update env x v2, pureMode := true }⟩)) := by
  cases h with
  | appArg => exact ⟨_, rfl, Or.inl rfl⟩
  | appFun h1 h2 => exact ⟨_, rfl, Or.inr (Or.inl ⟨_, _, _, h1, h2, rfl⟩)⟩
  | appFnBody h1 h2 h3 h4 h5 h6 =>
    exact ⟨_, rfl, Or.inr (Or.inr (Or.inl
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, rfl⟩))⟩
  | appPfnBody h1 h2 h3 h4 h5 h6 h7 =>
    exact ⟨_, rfl, Or.inr (Or.inr (Or.inr
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, h1, h2, h3, h4, h5, h6, h7,
        rfl⟩))⟩

/-- The calls of an application step. A pure call declares no effects. -/
theorem ExternCallAt.app_inv {ctx : TypeContext} {e1 e2 : Expr} {F : Nat} {cfg : Config}
    {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (h : ExternCallAt ⟨ctx, .app e1 e2, F, cfg⟩ effects entry res cf o) :
    ∃ G, F = G + 2 ∧
      ((∃ (r2 r1 : TypeResult) (c2 c1 : Config) (v2 vRaw : Value) (x y : Name) (env : VarEnv)
          (id : ExternId) (argTyp : Typ) (argPoison : Bool) (argPred : SyntaxPredicate)
          (retSpec : ExternReturn) (captures memberCaptures : List Capture)
          (st1 st2 : Typ) (p : Poison) (tcls : List PFnTClosure) (tenv : CapturedVarEnv)
          (declaredArgQt : QTyp) (cursor : Tag × Loc)
          (implFn : VarEnv → Value → Memory → Except ExternError Value),
        typecheckExpr ctx e2 G = .ok r2 ∧ terminatesTo e2 cfg c2 v2 ∧
        typecheckExpr (ctxAfter ctx r2) e1 G = .ok r1 ∧
        terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1
          (.peClosure x (.externPfn id y argTyp argPoison argPred retSpec captures) env) ∧
        r1.qualType.etyp = .parrow st1 st2 p tcls ∧
        ThreadedAt (pfnApply ctx r2 r1 st1 st2 p G) tcls (r1.nextTag', r1.nextLoc')
          (.extern id x retSpec tenv declaredArgQt memberCaptures) cursor res ∧
        c1.registry.get? id = some (.pfn implFn) ∧
        valueMatchesTyp v2 argTyp = true ∧
        implFn (env.update x v2) v2 c1.memory = .ok vRaw ∧
        validateExternReturn id retSpec vRaw = .ok o ∧
        effects = [] ∧
        entry = ExternCallEntry.ofRuntime (pfnBodyCtx ctx r2 r1 p x tenv cursor) c1 env x v2 ∧
        cf = c1) ∨
       (∃ (r2 r1 : TypeResult) (c2 c1 : Config) (v2 : Value) (x y : Name) (env : VarEnv)
          (id : ExternId) (argTyp : Typ) (argPoison : Bool) (argPred : SyntaxPredicate)
          (retSpec : ExternReturn) (effs : List Effect) (captures : List Capture),
        typecheckExpr ctx e2 G = .ok r2 ∧ terminatesTo e2 cfg c2 v2 ∧
        typecheckExpr (ctxAfter ctx r2) e1 G = .ok r1 ∧
        terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1
          (.closure x (.externFn id y argTyp argPoison argPred retSpec effs captures) env))) := by
  cases h with
  | pfn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact ⟨_, rfl, Or.inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, rfl, rfl, rfl⟩⟩
  | fn h1 h2 h3 h4 =>
    exact ⟨_, rfl, Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4⟩⟩

/-- The expression has no application and no `extern val` declaration at a
    place that a step recurses into (the bodies of `fn` and `pfn` are entered
    only from an application). -/
def noApp : Expr → Bool
  | .app _ _ => false
  | .externVal .. => false
  | .op e1 _ e2 => noApp e1 && noApp e2
  | .unaryop _ e => noApp e
  | .newRef e => noApp e
  | .deref e => noApp e
  | .assign e1 e2 => noApp e1 && noApp e2
  | .seq e1 e2 => noApp e1 && noApp e2
  | .vlet _ e1 e2 => noApp e1 && noApp e2
  | .ite e1 e2 e3 => noApp e1 && noApp e2 && noApp e3
  | _ => true

theorem SubStep.noApp {s s' : Step} (h : SubStep s s') (hs : noApp s.e = true) :
    noApp s'.e = true := by
  cases h <;> simp_all [ExternCallsWitness.noApp]

theorem Reach.noApp {s s' : Step} (h : Reach s s') (hs : noApp s.e = true) :
    noApp s'.e = true := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact SubStep.noApp hstep ih

/-- No step below an expression without applications calls an extern. -/
theorem ExternCallAt.not_of_reach_noApp {s s' : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hs : noApp s.e = true) (hreach : Reach s s') :
    ¬ ExternCallAt s' effects entry res cf o := by
  intro h
  have hs' := Reach.noApp hreach hs
  cases h <;> simp [ExternCallsWitness.noApp] at hs'

/-- No step below such an expression declares an `extern val`. -/
theorem ExternValAt.not_of_reach_noApp {s s' : Step} {res : TypeResult} {cf : Config}
    {o : Value} (hs : noApp s.e = true) (hreach : Reach s s') :
    ¬ ExternValAt s' res cf o := by
  intro h
  have hs' := Reach.noApp hreach hs
  cases h
  simp [ExternCallsWitness.noApp] at hs'

/-! ## The extern `read` -/

/-- The guard `w => w >= 0` of the result of `read`. -/
def geGuard : SyntaxPredicate :=
  SyntaxPredicate.guardClosure ⟨0⟩ "w" (Expr.op (Expr.var "w") Op.gte (Expr.num 0))

def readRet : ExternReturn := ExternReturn.simple Typ.int true geGuard

/-- `extern pfn @7 b : int -> (int :> poisoned { 0, w => w >= 0 })`. With
    `ap = true` the argument may be poisoned. -/
def readD (ap : Bool) : Expr :=
  Expr.externPfn 7 "b" Typ.int ap SyntaxPredicate.noPred readRet []

/-- The implementation of `read`: the identity. -/
def idImpl : VarEnv → Value → Memory → Except ExternError Value := fun _ v _ => .ok v

/-- The registry with `read` at id 7. -/
def reg : ExternRegistry := emptyExternRegistry.insert 7 (.pfn idImpl)

theorem reg_get : reg.get? 7 = some (.pfn idImpl) := by simp [reg]

theorem reg_get' : reg[7]? = some (.pfn idImpl) := by simp [reg]

/-- The extern policy that gives the tag `k` of a call of `read` the value
    `f k` and gives the tags of every other extern no value. -/
def on7 (f : Tag → Bool) : ExternId → Tag → Option Bool :=
  fun id k => if id = 7 then some (f k) else none

/-- A poisoned integer with no guard. -/
def pInt : QTyp := ⟨ETyp.int, true, Predicate.noPred⟩

/-- The closure a declaration of `read` evaluates to under `env`. -/
def readClo (ap : Bool) (env : VarEnv) : Value := .peClosure "b" (readD ap) env

theorem toPExpr?_readD (ap : Bool) : Expr.toPExpr? (readD ap) = none := rfl

theorem run_var {cfg : Config} {x : Name} {v : Value} (h : cfg.varEnv.lookup x = some v) :
    terminatesTo (.var x) cfg cfg v :=
  ⟨1, false, by unfold beval; simp only [VarEnv.lookup] at h ⊢; simp [h]⟩

theorem run_num (cfg : Config) (n : Int) : terminatesTo (.num n) cfg cfg (.num n) :=
  ⟨1, false, by unfold beval; simp⟩

theorem run_readD (ap : Bool) (cfg : Config) (hreg : cfg.registry = reg) :
    terminatesTo (readD ap) cfg cfg (readClo ap cfg.varEnv) :=
  ⟨1, false, by unfold beval; simp [readD, hreg, reg_get', readClo]⟩

/-- A call of `read` on an integer returns it and leaves the configuration. -/
theorem run_readCall {fe arg : Expr} {cfgB : Config} {ap : Bool} {env : VarEnv} {n : Int}
    (hrunF : ∀ c, c.varEnv = cfgB.varEnv → terminatesTo fe c c (readClo ap env))
    (hrunA : terminatesTo arg cfgB cfgB (.num n))
    (hreg : cfgB.registry = reg) :
    terminatesTo (.app fe arg) cfgB cfgB (.num n) := by
  obtain ⟨nA, vbA, hA⟩ := hrunA
  obtain ⟨nF, vbF, hF⟩ := hrunF { cfgB with varEnv := cfgB.varEnv } rfl
  refine ⟨max nA nF + 1, false, ?_⟩
  have hA' := beval_mono nA _ _ vbA _ _ hA (max nA nF) false (le_max_left _ _)
  have hF' := beval_mono nF _ _ vbF _ _ hF (max nA nF) false (le_max_right _ _)
  unfold beval
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  rw [hA']
  simp only
  rw [hF']
  simp [readClo, readD, hreg, reg_get', idImpl, validateExternReturn, readRet, valueMatchesTyp]

/-! ## A call of `read` -/

def isParrow1 : ETyp → Bool
  | .parrow _ _ _ [_] => true
  | _ => false

def parrowS1 : ETyp → Typ
  | .parrow a _ _ _ => a
  | _ => Typ.int

def parrowS2 : ETyp → Typ
  | .parrow _ b _ _ => b
  | _ => Typ.int

def parrowP : ETyp → Poison
  | .parrow _ _ p _ => p
  | _ => false

def parrowM : ETyp → PFnTClosure
  | .parrow _ _ _ [m] => m
  | _ => .regular "" .unit []

theorem parrow1_eq {E : ETyp} (h : isParrow1 E = true) :
    E = .parrow (parrowS1 E) (parrowS2 E) (parrowP E) [parrowM E] := by
  match E, h with
  | .parrow _ _ _ [_], _ => rfl

def extParts : PFnTClosure → CapturedVarEnv × QTyp × List Capture
  | .extern _ _ _ t q c => (t, q, c)
  | .regular _ _ _ => ([], ⟨.int, false, .noPred⟩, [])

theorem ThreadedAt.single_inv {α : Type} {f : α → Tag × Loc → TypecheckM TypeResult}
    {m x : α} {c c' : Tag × Loc} {r : TypeResult} (h : ThreadedAt f [m] c x c' r) :
    x = m ∧ c' = c ∧ f m c = .ok r := by
  cases h with
  | here h => exact ⟨rfl, rfl, h⟩
  | there _ h => cases h

theorem ThreadedAt.here_of_eq {α : Type} {f : α → Tag × Loc → TypecheckM TypeResult}
    {m m' : α} {rest : List α} {c : Tag × Loc} {r : TypeResult}
    (h : f m c = .ok r) (hm : m = m') : ThreadedAt f (m :: rest) c m' c r := by
  cases hm; exact .here h

/-- The typing of the parts of a call `fe arg` whose function evaluates to
    `read`: the argument, the function, the cursor of the one member, the
    member result and the body context. `G` is the fuel of the parts. -/
def iArg (B : TypeContext) (arg : Expr) (G : Nat) : TypeResult :=
  okVal (typecheckExpr B arg G)

def iFun (B : TypeContext) (fe arg : Expr) (G : Nat) : TypeResult :=
  okVal (typecheckExpr (ctxAfter B (iArg B arg G)) fe G)

def iCursor (B : TypeContext) (fe arg : Expr) (G : Nat) : Tag × Loc :=
  ((iFun B fe arg G).nextTag', (iFun B fe arg G).nextLoc')

def iRes (B : TypeContext) (fe arg : Expr) (G : Nat) : TypeResult :=
  let E := (iFun B fe arg G).qualType.etyp
  okVal (pfnApply B (iArg B arg G) (iFun B fe arg G) (parrowS1 E) (parrowS2 E) (parrowP E) G
    (parrowM E) (iCursor B fe arg G))

def iBody (B : TypeContext) (fe arg : Expr) (G : Nat) : TypeContext :=
  let E := (iFun B fe arg G).qualType.etyp
  pfnBodyCtx B (iArg B arg G) (iFun B fe arg G) (parrowP E) "b" (extParts (parrowM E)).1
    (iCursor B fe arg G)

/-- The parts of a call whose function evaluates to `read` have no applications
    when the function and the argument have none. -/
theorem readCall_sub {B : TypeContext} {fe arg : Expr} {F : Nat} {cfgB : Config}
    {ap : Bool} {env : VarEnv} {v : Value}
    (hfe : noApp fe = true) (harg : noApp arg = true)
    (hrunF : ∀ c, c.varEnv = cfgB.varEnv → terminatesTo fe c c (readClo ap env))
    (hrunA : terminatesTo arg cfgB cfgB v)
    {s' : Step} (h : SubStep ⟨B, .app fe arg, F, cfgB⟩ s') : noApp s'.e = true := by
  have hh := SubStep.app_inv h
  clear h
  obtain ⟨G, rfl, h⟩ := hh
  rcases h with h | h | h | h
  · subst h; exact harg
  · obtain ⟨_, _, _, _, _, rfl⟩ := h; exact hfe
  · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, body, env', st1, st2, p, tcls, tenv, cursor,
      hG, h2, hr2, h1, hr1, _⟩ := h
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    have := terminatesTo_det hr1 (hrunF _ rfl)
    simp [readClo] at this
  · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, body, pbody, env', st1, st2, p, tcls, tenv, cursor,
      hG, h2, hr2, h1, hr1, _, hpe, _⟩ := h
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    have := terminatesTo_det hr1 (hrunF _ rfl)
    simp only [readClo, Value.peClosure.injEq] at this
    obtain ⟨_, ⟨_, rfl, _⟩⟩ := this
    rw [toPExpr?_readD] at hpe
    cases hpe

/-- The one extern call of a call of `read` on `n`: it is typed against the
    member result `iRes`, returns `n` and leaves the configuration. The body
    context of its entry is `iBody` and its unified environment extends the
    captured environment of the closure by the argument. -/
theorem readCall_call {B : TypeContext} {fe arg : Expr} {G : Nat} {cfgB : Config}
    {ap : Bool} {env : VarEnv} {n : Int}
    (hrunF : ∀ c, c.varEnv = cfgB.varEnv → terminatesTo fe c c (readClo ap env))
    (hrunA : terminatesTo arg cfgB cfgB (.num n))
    (hreg : cfgB.registry = reg)
    (hok2 : isOkB (typecheckExpr B arg G) = true)
    (hok1 : isOkB (typecheckExpr (ctxAfter B (iArg B arg G)) fe G) = true)
    (hshape : isParrow1 (iFun B fe arg G).qualType.etyp = true)
    {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult} {cf : Config}
    {o : Value}
    (h : ExternCallAt ⟨B, .app fe arg, G + 2, cfgB⟩ effects entry res cf o) :
    res = iRes B fe arg G ∧ o = .num n ∧ cf = cfgB ∧ effects = [] ∧
      entry.bodyCtx = iBody B fe arg G ∧ entry.unifiedEnv = VarEnv.update env "b" (.num n) := by
  have hh := ExternCallAt.app_inv h
  clear h
  obtain ⟨G', hG, h⟩ := hh
  obtain rfl : G = G' := by omega
  rcases h with
    ⟨r2, r1, c2, c1, v2, vRaw, x, y, env', id, argTyp, argPoison, argPred, retSpec, captures,
      memberCaptures, st1, st2, p, tcls, tenv, declaredArgQt, cursor, implFn,
      h2, hr2, h1, hr1, hety, hthr, hregl, _, himpl, hval, rfl, rfl, rfl⟩ |
    ⟨r2, r1, c2, c1, v2, x, y, env', id, argTyp, argPoison, argPred, retSpec, effs, captures,
      h2, hr2, h1, hr1⟩
  · obtain rfl : r2 = iArg B arg G := ok_inj h2 (eq_okVal hok2)
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    obtain rfl : r1 = iFun B fe arg G := ok_inj h1 (eq_okVal hok1)
    obtain ⟨rfl, hc⟩ := terminatesTo_det hr1 (hrunF _ rfl)
    simp only [readClo, Value.peClosure.injEq, readD, Expr.externPfn.injEq] at hc
    obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := hc
    have hE := parrow1_eq hshape
    rw [hE] at hety
    simp only [ETyp.parrow.injEq] at hety
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hety
    obtain ⟨hm, rfl, happ⟩ := ThreadedAt.single_inv hthr
    refine ⟨(okVal_of_eq happ).symm, ?_, rfl, rfl, ?_, ?_⟩
    · simp only [hreg, reg_get, Option.some.injEq, ExternImpl.pfn.injEq] at hregl
      subst hregl
      simp only [idImpl, Except.ok.injEq] at himpl
      subst himpl
      simpa [validateExternReturn, readRet, valueMatchesTyp] using hval.symm
    · simp only [ExternCallEntry.ofRuntime, iBody, ← hm, extParts, iCursor]
    · rfl
  · obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    have := terminatesTo_det hr1 (hrunF _ rfl)
    simp [readClo] at this

/-- The typing of a call of `read` that realises its body context by the empty
    map: the member captures nothing and the argument is an `int`. -/
def ReadBodyEmpty (B : TypeContext) (fe arg : Expr) (G : Nat) : Prop :=
  (extParts (parrowM (iFun B fe arg G).qualType.etyp)).1 = [] ∧
    (iArg B arg G).qualType.etyp = ETyp.int

/-- The empty map realises the body context of the entry of a call of `read`
    whose typing satisfies `ReadBodyEmpty`: the body context binds the argument
    `"b"` to an `int` and nothing else, and the unified environment binds `"b"`
    to the integer argument. -/
theorem readCall_realised {B : TypeContext} {fe arg : Expr} {G : Nat} {cfgB : Config}
    {ap : Bool} {env : VarEnv} {n : Int}
    (hrunF : ∀ c, c.varEnv = cfgB.varEnv → terminatesTo fe c c (readClo ap env))
    (hrunA : terminatesTo arg cfgB cfgB (.num n))
    (hreg : cfgB.registry = reg)
    (hok2 : isOkB (typecheckExpr B arg G) = true)
    (hok1 : isOkB (typecheckExpr (ctxAfter B (iArg B arg G)) fe G) = true)
    (hshape : isParrow1 (iFun B fe arg G).qualType.etyp = true)
    (hb : ReadBodyEmpty B fe arg G)
    {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult} {cf : Config}
    {o : Value}
    (h : ExternCallAt ⟨B, .app fe arg, G + 2, cfgB⟩ effects entry res cf o) :
    runtimeInstantiatesCtx entry.bodyCtx entry.bodyConfig.memory entry.unifiedEnv ∅ := by
  obtain ⟨_, _, _, _, hbody, hun⟩ := readCall_call hrunF hrunA hreg hok2 hok1 hshape h
  refine ⟨fun l a hl => ?_, fun {x qt} hx => ?_⟩
  · simp [RealizationMap.lookup] at hl
  · rw [hbody] at hx
    simp only [iBody, pfnBodyCtx, hb.1] at hx
    by_cases hxb : x = "b"
    · subst hxb
      simp only [VarTypeEnv_lookup_update_eq, Option.some.injEq] at hx
      subst hx
      refine ⟨.num n, ?_, ?_⟩
      · rw [hun]; simp [VarEnv.update, VarEnv.lookup]
      · show valueHasETyp ∅ (.num n) (iArg B arg G).qualType.etyp
        rw [hb.2]; exact valueHasETyp.num n
    · rw [VarTypeEnv_lookup_update_ne _ "b" x _ hxb] at hx
      simp [VarTypeEnv.ofCaptured, VarTypeEnv.lookup] at hx

/-- The extern call of a call of `read` on `n`, built from the computed typing. -/
theorem readCall_mk {B : TypeContext} {fe arg : Expr} {G : Nat} {cfgB : Config}
    {ap : Bool} {env : VarEnv} {n : Int}
    (hrunF : ∀ c, c.varEnv = cfgB.varEnv → terminatesTo fe c c (readClo ap env))
    (hrunA : terminatesTo arg cfgB cfgB (.num n))
    (hreg : cfgB.registry = reg)
    (hok2 : isOkB (typecheckExpr B arg G) = true)
    (hok1 : isOkB (typecheckExpr (ctxAfter B (iArg B arg G)) fe G) = true)
    (hshape : isParrow1 (iFun B fe arg G).qualType.etyp = true)
    (hm : let E := (iFun B fe arg G).qualType.etyp
      parrowM E = .extern 7 "b" readRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
        (extParts (parrowM E)).2.2)
    (hap : let E := (iFun B fe arg G).qualType.etyp
      isOkB (pfnApply B (iArg B arg G) (iFun B fe arg G) (parrowS1 E) (parrowS2 E) (parrowP E) G
        (parrowM E) (iCursor B fe arg G)) = true) :
    ∃ entry, entry.bodyCtx = iBody B fe arg G ∧
      ExternCallAt ⟨B, .app fe arg, G + 2, cfgB⟩ [] entry (iRes B fe arg G) cfgB (.num n) := by
  have hr1 : terminatesTo fe { cfgB with varEnv := cfgB.varEnv } { cfgB with varEnv := cfgB.varEnv }
      (.peClosure "b" (.externPfn 7 "b" Typ.int ap .noPred readRet []) env) :=
    hrunF _ rfl
  have hregl :
      ({ cfgB with varEnv := cfgB.varEnv } : Config).registry.get? 7 = some (.pfn idImpl) := by
    show cfgB.registry.get? 7 = _
    rw [hreg]; exact reg_get
  exact ⟨_, rfl, ExternCallAt.pfn (eq_okVal hok2) hrunA (eq_okVal hok1) hr1 (parrow1_eq hshape)
    (ThreadedAt.here_of_eq (eq_okVal hap) hm) hregl rfl rfl
    (by simp [validateExternReturn, readRet, valueMatchesTyp])⟩

/-! ## The premises at one call -/

def guardAt (p : Predicate) (t : Tag) : Bool :=
  match p with
  | .guardClosure k _ _ _ => k == t
  | _ => false

theorem guardAt_spec {p : Predicate} {t : Tag} (h : guardAt p t = true) :
    ∃ a b c, p = .guardClosure t a b c := by
  unfold guardAt at h
  split at h
  · simp only [beq_iff_eq] at h; subst h; exact ⟨_, _, _, rfl⟩
  · cases h

/-- *Match* at a call that allocated the one tag `k`, returned `n`, and whose
    regime entry is `b`. -/
theorem callMatches_of {predSat : PredSat} {P : TagMeaning} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config}
    {k : Tag} {n : Int} {b : Bool} (hlaws : PredSatLaws predSat P) (hd : descGe P k = true)
    (ht : res.tagLog'.map (·.tag) = [k]) (hr : res.regime'.lookup? k = some b)
    (hb : (0 ≤ n ↔ b = true)) : CallMatches predSat entry [] res cf (.num n) := by
  refine ⟨?_, fun _ _ _ _ hc => absurd hc EffectCell.not_nil⟩
  intro a ha _ _ _ b' _ hreg θ _
  have hmem : a.tag ∈ res.tagLog'.map (·.tag) := List.mem_map_of_mem ha
  rw [ht, List.mem_singleton] at hmem
  rw [hmem] at hreg ⊢
  rw [hr] at hreg
  cases hreg
  rw [pin hlaws hd]
  exact hb

/-- *Match* fails at a reachable call that allocated the one tag `k`, whose
    regime entry is true, and that returned a negative value, when some
    realisation map `θ` realises the body context of the call. -/
theorem refute_of {predSat : PredSat} {P : TagMeaning} {root s : Step}
    {effects : List Effect} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config} {k : Tag} {n : Int} {θ : RealizationMap}
    (hlaws : PredSatLaws predSat P) (hd : descGe P k = true)
    (hθ : runtimeInstantiatesCtx entry.bodyCtx entry.bodyConfig.memory entry.unifiedEnv θ)
    (hreach : Reach root s) (hcall : ExternCallAt s effects entry res cf (.num n))
    (ht : res.tagLog'.map (·.tag) = [k]) (hg : guardAt res.qualType.pred k = true)
    (hr : res.regime'.lookup? k = some true) (hn : n < 0) :
    ¬ ExternCallsMatch predSat root := by
  intro hm
  have hcm := hm.calls _ _ _ _ _ _ hreach hcall
  obtain ⟨argName, body, cap, hpred⟩ := guardAt_spec hg
  have hmem : k ∈ res.tagLog'.map (·.tag) := by rw [ht]; simp
  obtain ⟨a, ha, hat⟩ := List.mem_map.mp hmem
  have h := hcm.ret a ha argName body cap true (by rw [hat]; exact hpred) (by rw [hat]; exact hr)
    θ hθ
  rw [hat, pin hlaws hd] at h
  simp at h
  omega

/-- *Agreement* fails at a call that both runs make, that allocated the one
    tag `k`, whose regime entry is true, whose result is an integer guarded by
    `k`, and that returned different values. -/
theorem callAgrees_false {entry₀ entry₁ : ExternCallEntry} {effects : List Effect}
    {res : TypeResult} {cf₀ cf₁ : Config} {k : Tag} {o₀ o₁ : Value}
    (ht : res.tagLog'.map (·.tag) = [k]) (hg : qtypGuardTag res.qualType = some k)
    (hr : res.regime'.lookup? k = some true) (hety : res.qualType.etyp = ETyp.int)
    (hne : o₀ ≠ o₁) : ¬ CallAgrees entry₀ entry₁ effects res cf₀ cf₁ o₀ o₁ := by
  intro hag
  have hmem : k ∈ res.tagLog'.map (·.tag) := by rw [ht]; simp
  obtain ⟨a, ha, hat⟩ := List.mem_map.mp hmem
  exact hne (hag.ret a ha (by rw [hat]; exact hg) (by rw [hat]; exact hr) (by rw [hety]; rfl)
    (by rw [hety]; rintro ⟨_, h⟩; cases h))

/-- Two member results that allocated different single tags differ. -/
theorem ne_of_tags {r₁ r₂ : TypeResult} {k₁ k₂ : Tag} (h₁ : r₁.tagLog'.map (·.tag) = [k₁])
    (h₂ : r₂.tagLog'.map (·.tag) = [k₂]) (hk : k₁ ≠ k₂) : r₁ ≠ r₂ := by
  rintro rfl
  rw [h₁] at h₂
  simp only [List.cons.injEq, and_true] at h₂
  exact hk h₂

/-- *Agreement* at a call without effects whose two runs return the same
    value. -/
theorem callAgrees_nil {entry₀ entry₁ : ExternCallEntry} {res : TypeResult} {cf₀ cf₁ : Config}
    {o₀ o₁ : Value} (h : o₀ = o₁) : CallAgrees entry₀ entry₁ [] res cf₀ cf₁ o₀ o₁ :=
  ⟨fun _ _ _ _ _ _ => h, fun _ _ _ _ _ _ hc => absurd hc EffectCell.not_nil⟩

/-- *Agreement* holds for two copies of one run when the calls of the run have
    no effects and the member result of a call fixes the value it returns. -/
theorem agree_self_of {root : Step}
    (h : ∀ s₀ s₁ effects entry₀ entry₁ res cf₀ cf₁ o₀ o₁, Reach root s₀ → Reach root s₁ →
      ExternCallAt s₀ effects entry₀ res cf₀ o₀ → ExternCallAt s₁ effects entry₁ res cf₁ o₁ →
      effects = [] ∧ o₀ = o₁) :
    ExternCallsAgree root root := by
  refine ⟨?_⟩
  intro s₀ s₁ _ _ _ _ _ _ _ _ hr₀ hr₁ _ _ _ hc₀ hc₁ _
  obtain ⟨rfl, ho⟩ := h _ _ _ _ _ _ _ _ _ _ hr₀ hr₁ hc₀ hc₁
  exact callAgrees_nil ho

end ExternCallsWitness
