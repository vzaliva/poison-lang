/-
  ExternCallsWitnessValCellWrite.lean - A write to a cell that the guard does not read,
  and the theorem applied to a program that declares the guarded `extern val` of
  `ExternCallsWitnessValCell` and writes between the declaration and the test.

  The program
      let a = ref 5 in
      let b = ref 0 in
      let v = extern val @251 : (int :> poisoned { 0, w => w > !a }) in
      let u = (b := 1) in
      if v > !a then v else 0
  allocates the cell of `a` at location `0` and the cell of `b` at location `1`. The
  record of the guard's tag is `{0}`: the guard reads the cell of `a` only. The write
  `b := 1`, to location `1`, keeps the tag in the regime, and the test `v > !a` is typed
  by the matched guard: under either value of the tag the program is typed as a clean
  `int`, and the tag keeps the value of the assignment in the regime (`typing_case`).
  The write `a := 6`, to location `0`, makes the result a poisoned `int`
  (`write_a_poisoned`).

  * The trusted entry `vSpec` of `@251`, the relation `cellSat` and its laws
    (`cellSat_lawful`), and the premises on the starting context are those of
    `ExternCallsWitnessValCell`.
  * *Match* of the declared value holds exactly when `5 < m ↔ b = true`
    (`match_iff`): at the declaration the cell of `a`, which the realisation map gives
    to location `0`, holds 5; the runs make no extern call (`agree`).
  * `same_return`: under an assignment where the value matches, two runs from any
    poisoned `x`, which the program does not read, return the same value. Every
    premise of `TypeSystemEnforcesFaultRobustness` is proved. The instances `true_7`
    and `false_3` exhibit runs that meet every premise; they end with the cell of `b`
    holding 1.

  Imports `ExternCallsWitnessValCell`; not on the FR proof path.
-/
import LeanProofs.ExternCallsWitnessValCell

open Std LeanPoison
open ExternCallsWitness.ValCell

namespace ExternCallsWitness

namespace ValCellWrite

/-! ## The programs -/

/-- `let a = ref 5 in let b = ref 0 in let v = extern val @251 : ... in
    let u = (b := 1) in if v > !a then v else 0` -/
def progC : Expr :=
  .vlet "a" (.newRef (.num 5)) (.vlet "b" (.newRef (.num 0))
    (.vlet "v" valD (.vlet "u" (.assign (.var "b") (.num 1)) test)))

/-- The same with `a := 6` in place of `b := 1`. -/
def progW : Expr :=
  .vlet "a" (.newRef (.num 5)) (.vlet "b" (.newRef (.num 0))
    (.vlet "v" valD (.vlet "u" (.assign (.var "a") (.num 6)) test)))

/-- The location `1`, as the type of `b`. -/
private def cS1 : LocSet := LocSet.singleton 1
private def cRef1 : QTyp := { etyp := ETyp.ref cS1, poison := false, pred := Predicate.noPred }

/-- The typing of `ref 0` in the context after the binding of `a`. -/
private def rB (b : Bool) : TypeResult := okVal (typecheckExpr (ctxA b) (.newRef (.num 0)) 56)

/-- The context after the binding of `b`. -/
private def ctxB (b : Bool) : TypeContext :=
  { ctxAfter (ctxA b) (rB b) with varEnv := (ctxA b).varEnv.update "b" (rB b).qualType }

/-- The typing of the declaration in the context after the binding of `b`. -/
private def rV (b : Bool) : TypeResult := okVal (typecheckExpr (ctxB b) valD 54)

/-- The typing of the program from the starting context. -/
def rootC (b : Bool) : TypeResult := okVal (typecheckExpr (K b) progC 60)

/-- The checks of the typing facts, by evaluation. -/
private def factsC (b : Bool) : Bool :=
  isOkB (typecheckExpr (K b) progC 60) &&
  isOkB (typecheckExpr (ctxA b) (.newRef (.num 0)) 56) &&
  decide ((rB b).qualType = cRef1) &&
  (ctxB b).memEnv.contains 0 &&
  (ctxB b).memEnv.contains 1 &&
  ((ctxB b).nextTag == 0) &&
  isOkB (typecheckExpr (ctxB b) valD 54) &&
  ((rV b).regime'.lookup? 0 == some b) &&
  logOk (rootC b).tagLog' &&
  ((rootC b).qualType.etyp == ETyp.int) &&
  ((rootC b).qualType.poison == false) &&
  ((rootC b).regime'.lookup? 0 == some b) &&
  ((rootC b).tagEnv'.toList.map (fun q => (q.1, q.2.deps.toList)) == [(0, [0])])

private theorem factsC_ok (b : Bool) : factsC b = true := by
  cases b <;> decide +kernel

private structure FactsC (b : Bool) : Prop where
  root : typecheckExpr (K b) progC 60 = .ok (rootC b)
  newref : typecheckExpr (ctxA b) (.newRef (.num 0)) 56 = .ok (rB b)
  rB_qt : (rB b).qualType = cRef1
  mem0 : (ctxB b).memEnv.contains 0 = true
  mem1 : (ctxB b).memEnv.contains 1 = true
  nextTag0 : (ctxB b).nextTag = 0
  decl : typecheckExpr (ctxB b) valD 54 = .ok (rV b)
  regime0 : (rV b).regime'.lookup? 0 = some b
  log : logOk (rootC b).tagLog' = true
  etyp : (rootC b).qualType.etyp = .int
  poison : (rootC b).qualType.poison = false
  regime : (rootC b).regime'.lookup? 0 = some b
  tagEnv : (rootC b).tagEnv'.toList.map (fun q => (q.1, q.2.deps.toList)) = [(0, [0])]

private theorem factsC_of (b : Bool) : FactsC b := by
  have hf := factsC_ok b
  simp only [factsC, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hf
  exact ⟨eq_okVal h1, eq_okVal h2, h3, h4, h5, h6, eq_okVal h7, h8, h9, h10, h11, h12, h13⟩

private theorem rV_facts (b : Bool) : VFacts (ctxB b) (rV b) := by
  have h := (factsC_of b).decl
  exact v_facts_of (fuel := 53) (poison := true) (by simpa [typecheckExpr, valD] using h)

/-! ## The runs -/

/-- The state after `ref 0`: the cell at address 1 holds 0. -/
private def cB (m n : Int) : Config :=
  { cfgA m n with memory := (cfgA m n).memory.update 1 0, nextAddr := 2 }

/-- The state at the declaration: `b` is bound to the address 1. -/
private def cfgB (m n : Int) : Config :=
  { cB m n with varEnv := (cfgA m n).varEnv.update "b" (.loc 1) }

/-- The final state of a run: the cell of `a` holds 5, the cell of `b` holds 1. -/
def cC (m n : Int) : Config :=
  { cfgX m n with memory := ((∅ : Memory).update 0 5).update 1 1, nextAddr := 2 }

private theorem run_newRef0 (m n : Int) :
    terminatesTo (.newRef (.num 0)) (cfgA m n) (cB m n) (.loc 1) :=
  ⟨3, false, by simp [beval, freshAddr, cB, cfgA, cA, cfgX]⟩

/-- The declaration returns the value of the registry and leaves the state. -/
private theorem run_valD (m n : Int) : terminatesTo valD (cfgB m n) (cfgB m n) (.num m) :=
  ⟨1, false, by simp [beval, valD, cfgB, cB, cfgA, cA, cfgX, regA, valueMatchesTyp]⟩

private theorem insert_twice (μ : Memory) (a : Address) (v w : Int) :
    (μ.insert a v).insert a w = μ.insert a w := by
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [Std.ExtTreeMap.getElem?_insert]
  split <;> simp_all

private theorem memB0 (m n : Int) : (cfgB m n).memory.lookup 0 = some 5 := by
  simp [cfgB, cB, cfgA, cA, cfgX, Memory.lookup, Memory.update, Std.ExtTreeMap.getElem_insert]

/-- A run with the value `m > 5` returns `m`. -/
private theorem run_progC_gt (m n : Int) (hm : 5 < m) :
    terminatesTo progC (cfgX m n) (cC m n) (.num m) := by
  refine ⟨14, false, ?_⟩
  simp [progC, valD, test, beval, freshAddr, cC, cfgX, regA, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, hm, Memory.update, Std.ExtTreeMap.getElem_insert,
    insert_twice]

/-- A run with the value `m ≤ 5` returns `0`. -/
private theorem run_progC_le (m n : Int) (hm : m ≤ 5) :
    terminatesTo progC (cfgX m n) (cC m n) (.num 0) := by
  refine ⟨14, false, ?_⟩
  simp [progC, valD, test, beval, freshAddr, cC, cfgX, regA, valueMatchesTyp, VarEnv.lookup,
    VarEnv.update, evalOp, List.lookup, Int.not_lt.mpr hm, Memory.update,
    Std.ExtTreeMap.getElem_insert, insert_twice]

/-! ## Inversion -/

/-- The root step, the steps of the bodies of `a` and `b`, and the declaration step. -/
def U0 (b : Bool) (m n : Int) : Step := ⟨K b, progC, 60, cfgX m n⟩
private def U1 (b : Bool) (m n : Int) : Step :=
  ⟨ctxA b, .vlet "b" (.newRef (.num 0))
    (.vlet "v" valD (.vlet "u" (.assign (.var "b") (.num 1)) test)), 58, cfgA m n⟩
private def U2 (b : Bool) (m n : Int) : Step :=
  ⟨ctxB b, .vlet "v" valD (.vlet "u" (.assign (.var "b") (.num 1)) test), 56, cfgB m n⟩
private def U3 (b : Bool) (m n : Int) : Step := ⟨ctxB b, valD, 54, cfgB m n⟩

private inductive InSetC (b : Bool) (m n : Int) : Step → Prop
  | u0 : InSetC b m n (U0 b m n)
  | u1 : InSetC b m n (U1 b m n)
  | u2 : InSetC b m n (U2 b m n)
  | u3 : InSetC b m n (U3 b m n)
  | leaf {s : Step} : noApp s.e = true → InSetC b m n s

private theorem inSetC_step {b : Bool} {m n : Int} {s s' : Step} (hs : InSetC b m n s)
    (h : SubStep s s') : InSetC b m n s' := by
  cases hs with
  | u0 =>
      have hh := SubStep.vlet_inv (ctx := K b) (x := "a") (e1 := .newRef (.num 5))
        (e2 := .vlet "b" (.newRef (.num 0))
          (.vlet "v" valD (.vlet "u" (.assign (.var "b") (.num 1)) test)))
        (F := 60) (cfg := cfgX m n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r, c, v, hr, hc, rfl⟩
      · exact InSetC.leaf rfl
      · obtain rfl : r = rN b := ok_inj hr (facts_of b).newref
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hc (run_newRef m n)
        exact InSetC.u1
  | u1 =>
      have hh := SubStep.vlet_inv (ctx := ctxA b) (x := "b") (e1 := .newRef (.num 0))
        (e2 := .vlet "v" valD (.vlet "u" (.assign (.var "b") (.num 1)) test))
        (F := 58) (cfg := cfgA m n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨r, c, v, hr, hc, rfl⟩
      · exact InSetC.leaf rfl
      · obtain rfl : r = rB b := ok_inj hr (factsC_of b).newref
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hc (run_newRef0 m n)
        exact InSetC.u2
  | u2 =>
      have hh := SubStep.vlet_inv (ctx := ctxB b) (x := "v") (e1 := valD)
        (e2 := .vlet "u" (.assign (.var "b") (.num 1)) test) (F := 56) (cfg := cfgB m n) h
      clear h
      obtain ⟨f, hF, h⟩ := hh
      obtain rfl : f = 54 := by omega
      rcases h with rfl | ⟨_, _, _, _, _, rfl⟩
      · exact InSetC.u3
      · exact InSetC.leaf rfl
  | u3 => cases h
  | leaf hl => exact InSetC.leaf (SubStep.noApp h hl)

private theorem inSetC_reach {b : Bool} {m n : Int} {s : Step} (h : Reach (U0 b m n) s) :
    InSetC b m n s := by
  induction h with
  | refl => exact InSetC.u0
  | tail _ hsub ih => exact inSetC_step ih hsub

/-- The run makes no extern call. -/
private theorem inSetC_call {b : Bool} {m n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSetC b m n s) : ¬ ExternCallAt s effects entry res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternCallAt.not_of_reach_noApp hl (Reach.refl _) h
  | _ => cases h

/-- The run declares the extern value once, at `U3`. -/
private theorem inSetC_val {b : Bool} {m n : Int} {s : Step} {res : TypeResult} {cf : Config}
    {o : Value} (hs : InSetC b m n s) (h : ExternValAt s res cf o) :
    res = rV b ∧ cf = cfgB m n ∧ o = .num m ∧ s = U3 b m n := by
  cases hs with
  | leaf hl => exact absurd h (ExternValAt.not_of_reach_noApp hl (Reach.refl _))
  | u0 => cases h
  | u1 => cases h
  | u2 => cases h
  | u3 =>
      cases h with
      | mk htc hrun =>
          obtain rfl := ok_inj htc (factsC_of b).decl
          obtain ⟨rfl, rfl⟩ := terminatesTo_det hrun (run_valD m n)
          exact ⟨rfl, rfl, rfl, rfl⟩

private theorem reach_1 (b : Bool) (m n : Int) : Reach (U0 b m n) (U1 b m n) :=
  Relation.ReflTransGen.single (SubStep.vletBody (facts_of b).newref (run_newRef m n))

private theorem reach_2 (b : Bool) (m n : Int) : Reach (U0 b m n) (U2 b m n) :=
  Relation.ReflTransGen.tail (reach_1 b m n)
    (SubStep.vletBody (factsC_of b).newref (run_newRef0 m n))

private theorem reach_3 (b : Bool) (m n : Int) : Reach (U0 b m n) (U3 b m n) :=
  Relation.ReflTransGen.tail (reach_2 b m n) SubStep.vletBound

private theorem val_mk (b : Bool) (m n : Int) :
    ExternValAt (U3 b m n) (rV b) (cfgB m n) (.num m) :=
  ExternValAt.mk (factsC_of b).decl (run_valD m n)

/-! ## The premises on the extern calls -/

/-- The realisation map of the context at the declaration: `0 ↦ 0` and `1 ↦ 1`. -/
private def θ01 : RealizationMap := θ0.insert 1 1

private theorem θ01_lookup {l : Loc} {a : Address} (h : θ01.lookup l = some a) :
    (l = 0 ∧ a = 0) ∨ (l = 1 ∧ a = 1) := by
  simp only [θ01, θ0, RealizationMap.lookup, Std.ExtTreeMap.get?_eq_getElem?] at h
  by_cases hl : l = 1
  · subst hl
    rw [Std.ExtTreeMap.getElem?_insert_self] at h
    simp at h
    exact Or.inr ⟨rfl, h.symm⟩
  · have hc : ¬ compare 1 l = Ordering.eq := by
      intro hc; exact hl ((Nat.compare_eq_eq).1 hc).symm
    rw [Std.ExtTreeMap.getElem?_insert] at h
    simp only [hc, ite_false] at h
    by_cases hl0 : l = 0
    · subst hl0
      rw [Std.ExtTreeMap.getElem?_insert_self] at h
      simp at h
      exact Or.inl ⟨rfl, h.symm⟩
    · have hc0 : ¬ compare 0 l = Ordering.eq := by
        intro hc0; exact hl0 ((Nat.compare_eq_eq).1 hc0).symm
      rw [Std.ExtTreeMap.getElem?_insert] at h
      simp [hc0] at h

private theorem θ01_zero : θ01.lookup 0 = some 0 := by
  simp [θ01, θ0, RealizationMap.lookup, Std.ExtTreeMap.getElem_insert]

private theorem θ01_one : θ01.lookup 1 = some 1 := by
  simp [θ01, RealizationMap.lookup]

private theorem ctxB_a (b : Bool) : (ctxB b).varEnv.lookup "a" = some cRef := by
  show ((ctxA b).varEnv.update "b" (rB b).qualType).lookup "a" = some cRef
  rw [VarTypeEnv_lookup_update_ne _ "b" "a" _ (by decide)]
  exact ctxA_a b

private theorem cfgB_a (m n : Int) : (cfgB m n).varEnv.lookup "a" = some (Value.loc 0) := by
  simp [cfgB, cB, cfgA, cA, cfgX, VarEnv.update, VarEnv.lookup, List.lookup]

/-- The map `θ01` realises the context at the declaration in the state there: `a` and
    `b` hold the addresses 0 and 1, whose cells hold 5 and 0. -/
private theorem ricD (b : Bool) (m n : Int) :
    runtimeInstantiatesCtx (ctxB b) (cfgB m n).memory (cfgB m n).varEnv θ01 := by
  have hF := factsC_of b
  refine ⟨?_, ?_⟩
  · intro l a h
    rcases θ01_lookup h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hF.mem0, by simp [cfgB, cB, cfgA, cA, cfgX, Memory.update]⟩
    · exact ⟨hF.mem1, by simp [cfgB, cB, cfgA, cA, cfgX, Memory.update]⟩
  · intro x qt h
    have h' : ((ctxA b).varEnv.update "b" (rB b).qualType).lookup x = some qt := h
    by_cases hx : x = "b"
    · subst hx
      rw [VarTypeEnv_lookup_update_eq, Option.some.injEq] at h'
      subst h'
      rw [hF.rB_qt]
      refine ⟨Value.loc 1, by simp [cfgB, VarEnv.update, VarEnv.lookup], ?_⟩
      exact valueHasETyp.loc (l := 1) θ01_one (by simp [cS1, LocSet.singleton])
    · rw [VarTypeEnv_lookup_update_ne _ "b" x _ hx] at h'
      have h'' : ((K b).varEnv.update "a" (rN b).qualType).lookup x = some qt := h'
      by_cases hxa : x = "a"
      · subst hxa
        rw [VarTypeEnv_lookup_update_eq, Option.some.injEq] at h''
        subst h''
        rw [(facts_of b).rN_qt]
        refine ⟨Value.loc 0, cfgB_a m n, ?_⟩
        exact valueHasETyp.loc (l := 0) θ01_zero (by simp [cS0, LocSet.singleton])
      · rw [VarTypeEnv_lookup_update_ne _ "a" x _ hxa] at h''
        have hq := K_vars b x qt h''
        subst hq
        have hx' : x = "x" := by
          by_contra hx'
          simp only [K] at h''
          rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx'] at h''
          simp [VarTypeEnv.lookup] at h''
        subst hx'
        exact ⟨Value.num n, by simp [cfgB, cB, cfgA, cA, cfgX, VarEnv.update, VarEnv.lookup,
          List.lookup], valueHasETyp.num n⟩

/-- *Match* holds exactly when the value satisfies the guard as the assignment says: the
    cell of `a` holds 5 at the declaration, so `5 < m` when the tag is true and
    `m ≤ 5` when it is false. -/
theorem match_iff (b : Bool) (m n : Int) :
    ExternCallsMatch cellSat (U0 b m n) ↔ (5 < m ↔ b = true) := by
  have hF := factsC_of b
  have hf := rV_facts b
  constructor
  · intro h
    have hv := h.vals _ _ _ _ (reach_3 b m n) (val_mk b m n)
    obtain ⟨arg, body, cap, hp⟩ := hf.guard
    obtain ⟨a, ha, hat⟩ := hf.logged
    have hiff := hv a ha arg body cap b (by rw [hat]; exact hp)
      (by rw [hat, hF.nextTag0]; exact hF.regime0) θ01 (ricD b m n)
    rw [hat, hF.nextTag0] at hiff
    exact (cellSat_cell (k := 0) (μ := (cfgB m n).memory) (θ := θ01) θ01_zero
      (memB0 m n)).symm.trans hiff
  · intro hm
    refine ⟨fun _ _ _ _ _ _ hreach hcall => absurd hcall (inSetC_call (inSetC_reach hreach)),
      fun s res cf o hreach hval => ?_⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := inSetC_val (inSetC_reach hreach) hval
    intro a ha arg body cap b' hp hR θ hθ
    obtain ⟨arg', body', cap', hp'⟩ := hf.guard
    have hat : a.tag = 0 := by
      rw [hp'] at hp
      simp only [Predicate.guardClosure.injEq] at hp
      exact hp.1.symm.trans hF.nextTag0
    rw [hat] at hR ⊢
    rw [hF.regime0, Option.some.injEq] at hR
    subst hR
    have hθ0 : θ.lookup 0 = some 0 := a_at_zero (ctxB_a b) hθ (cfgB_a m n)
    rw [cellSat_cell hθ0 (memB0 m n)]
    exact hm

/-- *Agreement* holds for every pair of runs: they make no extern call. -/
theorem agree (b : Bool) (m n₀ n₁ : Int) : ExternCallsAgree (U0 b m n₀) (U0 b m n₁) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hr₀ _ _ _ _ hc₀ _ _ =>
    absurd hc₀ (inSetC_call (inSetC_reach hr₀))⟩

/-! ## The trusted entry, the theorem -/

private theorem inProg_asg {id : ExternId} {d : ExternDeclaration}
    (h : ExternDeclarationInProgram (.assign (.var "b") (.num 1)) id d) : False := by
  cases h with
  | assign_left h => cases h
  | assign_right h => cases h

private theorem trustedC (b : Bool) (m : Int) : InitialContextTrusted (vReg m) progC (K b) := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 251 ∧ d = vDecl := by
        simp only [progC, valD] at hp
        cases hp with
        | vlet_bound h => cases h with | newRef h => cases h
        | vlet_body h =>
            cases h with
            | vlet_bound h => cases h with | newRef h => cases h
            | vlet_body h =>
                cases h with
                | vlet_bound h => cases h; exact ⟨rfl, rfl⟩
                | vlet_body h =>
                    cases h with
                    | vlet_bound h => exact (inProg_asg h).elim
                    | vlet_body h => exact (inProg_test h).elim
      obtain ⟨rfl, rfl⟩ := h
      simp [vReg, TrustedRegistry.lookup?] at hlookup
      obtain ⟨_, rfl⟩ := hlookup
      rfl
  | var hlk hqt =>
      have hq := K_vars b _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt

/-- The typing and the premises: under both assignments the program is typed as a
    clean `int`, the guard is in the regime with the assignment's value and its record
    has the dependency set `{0}`, the laws hold of the program table, and *match* holds
    exactly when the cell and the value are as the assignment says. -/
theorem typing_case :
    (∀ b, typecheck (K b) progC 60 = .ok (rootC b) ∧
      (rootC b).qualType.etyp = .int ∧ (rootC b).qualType.poison = false ∧
      (rootC b).regime'.lookup? 0 = some b ∧
      (rootC b).tagEnv'.toList.map (fun q => (q.1, q.2.deps.toList)) = [(0, [0])] ∧
      PredSatLaws cellSat (programTable ∅ (rootC b).tagLog')) ∧
    ExternCallsMatch cellSat (U0 true 7 4) ∧ ExternCallsMatch cellSat (U0 false 3 4) ∧
    ¬ ExternCallsMatch cellSat (U0 false 7 4) ∧ ¬ ExternCallsMatch cellSat (U0 true 3 4) := by
  refine ⟨fun b => ?_, ?_, ?_, ?_, ?_⟩
  · have hF := factsC_of b
    exact ⟨hF.root, hF.etyp, hF.poison, hF.regime, hF.tagEnv,
      cellSat_lawful (cellTable_of_log hF.log)⟩
  · exact (match_iff true 7 4).2 (by decide)
  · exact (match_iff false 3 4).2 (by decide)
  · rw [match_iff false 7 4]; decide
  · rw [match_iff true 3 4]; decide

/-- **The theorem at `progC`**, the program that declares
    `extern val @251 : (int :> poisoned { 0, w => w > !a })` and writes `b := 1` before the
    test `if v > !a then v else 0`, under the assignment `b`, with the registry holding
    `m`: when the value satisfies the guard as the assignment says (`5 < m ↔ b = true`),
    two runs from any `x` return the same value. -/
theorem same_return (b : Bool) (m : Int) (hm : 5 < m ↔ b = true) (n₀ n₁ : Int)
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo progC (cfgX m n₀) cf₀ o₀)
    (hr₁ : terminatesTo progC (cfgX m n₁) cf₁ o₁) :
    o₀ = o₁ := by
  have hF := factsC_of b
  have hlaws := cellSat_lawful (cellTable_of_log hF.log)
  obtain ⟨_, _, _, _, hobs⟩ :=
    TypeSystemEnforcesFaultRobustness (vReg m) progC sV obsRet (K b) (externRegimeMatchesK b)
      (trustedC b m) wfSpecV rfl (ctxMatchesK b) (wfCtxK b) rfl rfl rfl (tagBoundedK b)
      (guardCapsK b) cellSat ∅ (wfTmK b) (tmBoundedK b) cellLaws_empty 60 (rootC b) hF.root
      (And.intro (fun et h => by
          simp only [obsRet, Option.some.injEq] at h
          subst h
          exact ⟨hF.etyp, hF.poison⟩)
        (fun _ _ h => by simp [obsRet, MemoryETypEnv.lookup] at h))
      hlaws ∅ ∅ _ _ ∅ ∅ 0 0 false cf₀ cf₁ o₀ o₁ (wfRegimeK b) wfθ₀ wfθ₀
      (wfCX m n₀) (wfCX m n₁) (reservedWFV m) (reservedWFV m) (disciplineK b m) (disciplineK b m)
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (instantiatesK b n₀) (instantiatesK b n₁) (trustedInitK b n₀) (trustedInitK b n₁)
      (consistentK b) (consistentK b) ((match_iff b m n₀).2 hm)
      ((match_iff b m n₁).2 hm) (agreeCriticalK b) (agreeTrustedK b)
      (agree b m n₀ n₁) hr₀ hr₁
  exact hobs.2

/-- **Tag true, value 7**: the runs from `x = 4` and `x = 5` both return 7. -/
theorem true_7 :
    terminatesTo progC (cfgX 7 4) (cC 7 4) (.num 7) ∧
    terminatesTo progC (cfgX 7 5) (cC 7 5) (.num 7) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo progC (cfgX 7 4) cf₀ o₀ → terminatesTo progC (cfgX 7 5) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_progC_gt 7 4 (by decide), run_progC_gt 7 5 (by decide),
    fun hr₀ hr₁ => same_return true 7 (by decide) 4 5 hr₀ hr₁⟩

/-- **Tag false, value 3**: the runs from `x = 4` and `x = 5` both return 0. -/
theorem false_3 :
    terminatesTo progC (cfgX 3 4) (cC 3 4) (.num 0) ∧
    terminatesTo progC (cfgX 3 5) (cC 3 5) (.num 0) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo progC (cfgX 3 4) cf₀ o₀ → terminatesTo progC (cfgX 3 5) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_progC_le 3 4 (by decide), run_progC_le 3 5 (by decide),
    fun hr₀ hr₁ => same_return false 3 (by decide) 4 5 hr₀ hr₁⟩

/-! ## The write to the cell of `a` -/

/-- The check that `progW` is typed as a poisoned `int`, by evaluation. -/
private def poisonedB (b : Bool) : Bool :=
  isOkB (typecheckExpr (K b) progW 60) &&
  ((okVal (typecheckExpr (K b) progW 60)).qualType.etyp == ETyp.int) &&
  ((okVal (typecheckExpr (K b) progW 60)).qualType.poison == true)

private theorem poisonedB_ok (b : Bool) : poisonedB b = true := by
  cases b <;> decide +kernel

/-- **The write to the cell of `a` makes the result poisoned**: under both assignments,
    `let a = ref 5 in let b = ref 0 in let v = extern val @251 : ... in let u = (a := 6) in
    if v > !a then v else 0` is typed as a poisoned `int`. -/
theorem write_a_poisoned (b : Bool) :
    ∃ r, typecheckExpr (K b) progW 60 = .ok r ∧ r.qualType.etyp = .int ∧
      r.qualType.poison = true := by
  have hf := poisonedB_ok b
  simp only [poisonedB, Bool.and_eq_true, beq_iff_eq] at hf
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  exact ⟨_, eq_okVal h1, h2, h3⟩

end ValCellWrite

end ExternCallsWitness
