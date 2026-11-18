import LeanProofs.ExternCallsWitnessBase

/-!
# The premises on extern calls for a cell written by an effect

`rd (ref x)`, with `x` a poisoned input of type `int` and `rd` an extern function
in the shape of `lp55xx_read`:

    extern fn @8 r : (ref int :> clean {}) -> (int :> poisoned { 0, w => w >= 0 }),
      effects: { !r :> (int :> poisoned { 0 }) }

The return guard and the cell written through the reference argument share the
tag index 0. The implementation reads the value `n` of the cell `r` points to,
writes `n / 2` to it and returns 0. The program passes it a fresh cell holding
`x`.

The call allocates tag 0, which the policy sets true. The typing of the call
stores `poisoned { 0 }` for the cell (`cell_found`): a guard without
predicate, which counts as clean when tag 0 is true. So *match* asks nothing
of the cell, and *agreement* asks the two runs to leave the same content in
it.

* `match_of`: *match* holds in every run, for every `predSat` that satisfies
  the laws on the program table: the call returns 0, which passes the check.
* `agree_iff`: *agreement* holds exactly when the two runs leave the same
  content in the cell, `x₀ / 2 = x₁ / 2`. The call returns 0 in every run, so
  the cell decides, and it is the content the call wrote that counts: the runs
  with `x = 4` and `x = 5` agree although they start with different contents.
* `cell_case` collects these facts: the runs 4 and 5 agree, 4 and 6 do not.
* `callAgrees_refl`: a call agrees with itself.

The typing facts are computed by the kernel (`decide +kernel`).

The trusted entry for `rd`, whose two-run call contract is proved from the
clause of *agreement* for cells, and the theorem applied to this program and
to one that reads the cell back are in `ExternCallsWitnessCellClosed`.

Limits. The cell's guard has no predicate, so the clause of *match* for a
cell whose guard carries one has no witness here.
-/

open Std LeanPoison

namespace ExternCallsWitness

namespace Cell

/-! ## The extern and the program -/

/-- The effect `!r :> (int :> poisoned { 0 })`. -/
def rdEff : Effect := ⟨.namedVar "r", true, .guardOnly ⟨0⟩⟩

/-- `extern fn @8 r : (ref int :> clean {}) -> (int :> poisoned { 0, w => w >= 0 })`,
    with the effect `rdEff`. -/
def rdD : Expr := .externFn 8 "r" (.ref .int) false .noPred readRet [rdEff] []

/-- The implementation: read the value `n` of the cell, write `n / 2`, return 0. -/
def rdImpl : VarEnv → Value → Memory → Address →
    Except ExternError (Value × Memory × Address) := fun _ v mem next =>
  match v with
  | .loc a =>
      match mem.lookup a with
      | some n => .ok (.num 0, mem.update a (n / 2), next)
      | none => .error (.shapeMismatch 8)
  | _ => .error (.shapeMismatch 8)

/-- The registry with `rd` at id 8. -/
def regC : ExternRegistry := emptyExternRegistry.insert 8 (.fn rdImpl)

/-- The registry holds `rd` at id 8. -/
theorem regC_get : regC.get? 8 = some (.fn rdImpl) := by simp [regC]

/-- The same, by indexing. -/
theorem regC_get' : regC[8]? = some (.fn rdImpl) := by simp [regC]

/-- The extern policy: every tag of a call of `rd` is true. -/
def pol : ExternId → Tag → Option Bool := fun id _ => if id = 8 then some true else none

/-- The argument `ref x` and the program. -/
def arg : Expr := .newRef (.var "x")
def prog : Expr := .app rdD arg

/-- The typing context: `x` is a poisoned integer. -/
def K0 : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅, varEnv := (∅ : VarTypeEnv).update "x" pInt,
    tagEnv := ∅, nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := pol }

/-! ## The typing of the call -/

/-- A function type with one member. -/
def isArrow1 : ETyp → Bool
  | .arrow _ _ _ [_] => true
  | _ => false

def arrowS1 : ETyp → Typ
  | .arrow a _ _ _ => a
  | _ => Typ.int

def arrowS2 : ETyp → Typ
  | .arrow _ b _ _ => b
  | _ => Typ.int

def arrowP : ETyp → Poison
  | .arrow _ _ p _ => p
  | _ => false

def arrowM : ETyp → FnTClosure
  | .arrow _ _ _ [m] => m
  | _ => .regular "" .unit []

/-- A function type with one member, by its parts. -/
theorem arrow1_eq {E : ETyp} (h : isArrow1 E = true) :
    E = .arrow (arrowS1 E) (arrowS2 E) (arrowP E) [arrowM E] := by
  match E, h with
  | .arrow _ _ _ [_], _ => rfl

def fExtParts : FnTClosure → CapturedVarEnv × QTyp × List Capture
  | .extern _ _ _ _ t q c => (t, q, c)
  | .regular _ _ _ => ([], ⟨.int, false, .noPred⟩, [])

/-- The typing of the argument, of the function, the cursor of the member,
    the member result and the body context. -/
def rArg : TypeResult := okVal (typecheckExpr K0 arg 58)
def rFun : TypeResult := okVal (typecheckExpr (ctxAfter K0 rArg) rdD 58)
def cur : Tag × Loc := (rFun.nextTag', rFun.nextLoc')
def bnd : Nat := rFun.nextBind'
def callRes : TypeResult :=
  let E := rFun.qualType.etyp
  okVal (fnApply K0 rArg rFun (arrowS1 E) (arrowS2 E) (arrowP E) 58 (arrowM E) cur bnd)
def body : TypeContext :=
  fnBodyCtx K0 rArg rFun (arrowP rFun.qualType.etyp) "r" (fExtParts (arrowM rFun.qualType.etyp)).1
    cur bnd
def rootRes : TypeResult := okVal (typecheckExpr K0 prog 60)

/-- The locations of a reference type. -/
def refLocs : Option QTyp → Option (List Loc)
  | some ⟨.ref ls, _, _⟩ => some ls.toList
  | _ => none

/-- The type `poisoned { k }` of an integer cell. -/
def cellQt : QTyp := ⟨.int, true, .guardOnly 0⟩

/-- The stored type is `poisoned { 0 }`. -/
def isCell : Option QTyp → Bool
  | some ⟨.int, true, .guardOnly k⟩ => k == 0
  | _ => false

/-- The stored type of a cell that passes `isCell`. -/
theorem isCell_eq {o : Option QTyp} (h : isCell o = true) : o = some cellQt := by
  match o, h with
  | some ⟨.int, true, .guardOnly k⟩, h =>
      simp only [isCell, beq_iff_eq] at h
      subst h
      rfl

private def facts : Bool :=
  isOkB (typecheckExpr K0 prog 60) &&
  isOkB (typecheckExpr K0 arg 58) &&
  isOkB (typecheckExpr (ctxAfter K0 rArg) rdD 58) &&
  isArrow1 rFun.qualType.etyp &&
  (callRes.tagLog'.map (·.tag) == [0]) &&
  (callRes.regime'.lookup? 0 == some true) &&
  (qtypGuardTag callRes.qualType == some 0) &&
  (callRes.qualType.etyp == ETyp.int) &&
  (refLocs (body.varEnv.lookup "r") == some [0]) &&
  isCell (callRes.memEnv'.lookup 0) &&
  descGe (programTable ∅ rootRes.tagLog') 0 &&
  allGe rootRes.tagLog'

private theorem facts_ok : facts = true := by decide +kernel

private theorem call_chain :
    let E := rFun.qualType.etyp
    arrowM E = .extern 8 "r" readRet [rdEff] (fExtParts (arrowM E)).1 (fExtParts (arrowM E)).2.1
      (fExtParts (arrowM E)).2.2 ∧
    isOkB (fnApply K0 rArg rFun (arrowS1 E) (arrowS2 E) (arrowP E) 58 (arrowM E) cur bnd) =
      true := by
  decide +kernel

/-! ## The run -/

/-- The start state with `x = n`. -/
def cfgX (n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update [] "x" (.num n), nextAddr := 0, pureMode := false,
    registry := regC }

/-- The state after `ref x`, in which `rd` is evaluated. -/
def cfgR (n : Int) : Config :=
  { cfgX n with memory := Memory.update ∅ 0 n, nextAddr := 1 }

/-- The state after the call. -/
def cfgF (n : Int) : Config :=
  { cfgR n with memory := Memory.update (Memory.update ∅ 0 n) 0 (n / 2), nextAddr := 1 }

/-- The call entry. -/
def entryOf (n : Int) : ExternCallEntry :=
  ExternCallEntry.ofRuntime body (cfgR n) (cfgX n).varEnv "r" (.loc 0)

/-- The root step. -/
def U0 (n : Int) : Step := ⟨K0, prog, 60, cfgX n⟩

/-- The run of `ref x` from `x = n` allocates the cell at address 0. -/
theorem run_arg (n : Int) : terminatesTo arg (cfgX n) (cfgR n) (.loc 0) :=
  ⟨2, false, by simp [arg, beval, cfgX, cfgR, freshAddr, VarEnv.lookup, VarEnv.update]⟩

/-- The implementation on the cell at address 0 holding `n`. -/
theorem rd_ok (E : VarEnv) (n : Int) :
    rdImpl E (.loc 0) (Memory.update ∅ 0 n) 1 =
      .ok (.num 0, Memory.update (Memory.update ∅ 0 n) 0 (n / 2), 1) := by
  simp [rdImpl, Memory.lookup, Memory.update]

/-- The declaration of `rd` evaluates to a closure. -/
theorem run_rd (c : Config) (hreg : c.registry = regC) :
    terminatesTo rdD c c (.closure "r" rdD c.varEnv) :=
  ⟨1, false, by unfold beval; simp [rdD, hreg, regC_get']⟩

/-! ## Inversion -/

/-- The calls of an application step whose function evaluates to a closure:
    the `fn` constructor of `ExternCallAt`, with all its premises. -/
theorem ExternCallAt.fn_inv {ctx : TypeContext} {e1 e2 : Expr} {F : Nat} {cfg : Config}
    {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (h : ExternCallAt ⟨ctx, .app e1 e2, F, cfg⟩ effects entry res cf o) :
    ∃ G, F = G + 2 ∧
      ((∃ (c2 c1 : Config) (v2 : Value) (x : Name) (b : Expr) (env : VarEnv),
          terminatesTo e2 cfg c2 v2 ∧
          terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1 (.peClosure x b env)) ∨
       (∃ (r2 r1 : TypeResult) (c2 c1 : Config) (v2 vRaw : Value) (x y : Name) (env : VarEnv)
          (id : ExternId) (argTyp : Typ) (argPoison : Bool) (argPred : SyntaxPredicate)
          (retSpec : ExternReturn) (effs : List Effect) (captures memberCaptures : List Capture)
          (st1 st2 : Typ) (p : Poison) (tcls : List FnTClosure) (tenv : CapturedVarEnv)
          (declaredArgQt : QTyp) (cursor : Tag × Loc) (bn : Nat)
          (implFn : VarEnv → Value → Memory → Address →
            Except ExternError (Value × Memory × Address))
          (mem' : Memory) (addr' : Address),
        typecheckExpr ctx e2 G = .ok r2 ∧ terminatesTo e2 cfg c2 v2 ∧
        typecheckExpr (ctxAfter ctx r2) e1 G = .ok r1 ∧
        terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1
          (.closure x (.externFn id y argTyp argPoison argPred retSpec effs captures) env) ∧
        r1.qualType.etyp = .arrow st1 st2 p tcls ∧
        ThreadedAt (fnApply ctx r2 r1 st1 st2 p G) tcls (r1.nextTag', r1.nextLoc')
          r1.nextBind' (.extern id x retSpec effs tenv declaredArgQt memberCaptures) cursor bn res ∧
        c1.pureMode = false ∧
        c1.registry.get? id = some (.fn implFn) ∧
        valueMatchesTyp v2 argTyp = true ∧
        implFn (env.update x v2) v2 c1.memory c1.nextAddr = .ok (vRaw, mem', addr') ∧
        validateExternReturn id retSpec vRaw = .ok o ∧
        effects = effs ∧
        entry = ExternCallEntry.ofRuntime (fnBodyCtx ctx r2 r1 p x tenv cursor bn) c1 env x v2 ∧
        cf = { c1 with memory := mem', nextAddr := addr' })) := by
  cases h with
  | pfn _ h2 _ h4 =>
    exact ⟨_, rfl, Or.inl ⟨_, _, _, _, _, _, h2, h4⟩⟩
  | fn h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    exact ⟨_, rfl, Or.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, rfl, rfl, rfl⟩⟩

/-- The steps the run reaches: the root, and steps without applications. -/
private inductive InSet (n : Int) : Step → Prop
  | u0 : InSet n (U0 n)
  | leaf {s : Step} : noAppIte s.e = true → InSet n s

private theorem inSet_step {n : Int} {s s' : Step} (hs : InSet n s) (h : SubStep s s') :
    InSet n s' := by
  cases hs with
  | u0 =>
      have hh := SubStep.app_inv (ctx := K0) (e1 := rdD) (e2 := arg) (F := 60) (cfg := cfgX n) h
      clear h
      obtain ⟨G, _, h⟩ := hh
      rcases h with rfl | ⟨_, _, _, _, _, rfl⟩ | h | h
      · exact InSet.leaf rfl
      · exact InSet.leaf rfl
      · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, b, env', st1, st2, p, tcls, tenv, cursor, bn,
          hG, h2, hr2, h1, hr1, _, _, rfl⟩ := h
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_arg n)
        have := terminatesTo_det hr1 (run_rd _ rfl)
        simp only [Value.closure.injEq] at this
        obtain ⟨_, _, rfl, _⟩ := this
        exact InSet.leaf rfl
      · obtain ⟨H, r2, r1, rb, c2, c1, v2, x, b, pb, env', st1, st2, p, tcls, tenv, cursor, bn,
          hG, h2, hr2, h1, hr1, _⟩ := h
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_arg n)
        have := terminatesTo_det hr1 (run_rd _ rfl)
        simp at this
  | leaf hl => exact InSet.leaf (SubStep.noAppIte h hl)

private theorem inSet_reach {n : Int} {s : Step} (h : Reach (U0 n) s) : InSet n s := by
  induction h with
  | refl => exact InSet.u0
  | tail _ hsub ih => exact inSet_step ih hsub

/-- The run makes one call, at the root: it is typed against `callRes`, has
    the effect `rdEff`, returns 0 and leaves the state `cfgF n`. -/
private theorem inSet_call {n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet n s) (h : ExternCallAt s effects entry res cf o) :
    effects = [rdEff] ∧ entry = entryOf n ∧ res = callRes ∧ cf = cfgF n ∧ o = .num 0 := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hok2, hok1, hshape, _⟩ := hf
  cases hs with
  | leaf hl =>
      exact absurd h (ExternCallAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _))
  | u0 =>
  have hh := ExternCallAt.fn_inv (ctx := K0) (e1 := rdD) (e2 := arg) (F := 60) (cfg := cfgX n) h
  clear h
  obtain ⟨G, hG, h⟩ := hh
  obtain rfl : G = 58 := by omega
  rcases h with ⟨c2, c1, v2, x, b, env, hr2, hr1⟩ |
    ⟨r2, r1, c2, c1, v2, vRaw, x, y, env, id, argTyp, argPoison, argPred, retSpec, effs,
      captures, memberCaptures, st1, st2, p, tcls, tenv, declaredArgQt, cursor, bn, implFn, mem',
      addr', h2, hr2, h1, hr1, hety, hthr, _, hregl, _, himpl, hval, rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_arg n)
    have := terminatesTo_det hr1 (run_rd _ rfl)
    simp at this
  · obtain rfl : r2 = rArg := ok_inj h2 (eq_okVal hok2)
    obtain ⟨rfl, rfl⟩ := terminatesTo_det hr2 (run_arg n)
    obtain rfl : r1 = rFun := ok_inj h1 (eq_okVal hok1)
    obtain ⟨rfl, hc⟩ := terminatesTo_det hr1 (run_rd _ rfl)
    simp only [rdD, Value.closure.injEq, Expr.externFn.injEq] at hc
    obtain ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ := hc
    have hE := arrow1_eq hshape
    rw [hE] at hety
    simp only [ETyp.arrow.injEq] at hety
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hety
    obtain ⟨hm, rfl, rfl, happ⟩ := ThreadedAt.single_inv hthr
    have hreg : implFn = rdImpl := by
      have : (cfgR n).registry.get? 8 = some (.fn rdImpl) := regC_get
      simp only [cfgR, cfgX] at hregl this
      rw [hregl] at this
      simpa using this
    subst hreg
    have hc := himpl.symm.trans (rd_ok _ n)
    simp only [Except.ok.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    refine ⟨rfl, ?_, (okVal_of_eq happ).symm, rfl, ?_⟩
    · simp only [entryOf, body, ← hm, fExtParts, cur, bnd]
      rfl
    · simpa [validateExternReturn, readRet, valueMatchesTyp] using hval.symm

/-- No step of the set declares an `extern val`. -/
private theorem inSet_val {n : Int} {s : Step} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet n s) : ¬ ExternValAt s res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternValAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _) h
  | _ => cases h

/-- The call at the root, built from the computed typing. -/
private theorem call_mk (n : Int) :
    ExternCallAt (U0 n) [rdEff] (entryOf n) callRes (cfgF n) (.num 0) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hok2, hok1, hshape, _⟩ := hf
  obtain ⟨hm, hap⟩ := call_chain
  have hr1 : terminatesTo rdD { cfgR n with varEnv := (cfgX n).varEnv }
      { cfgR n with varEnv := (cfgX n).varEnv } (.closure "r" rdD (cfgX n).varEnv) :=
    run_rd _ rfl
  exact ExternCallAt.fn (vRaw := .num 0) (mem' := Memory.update (Memory.update ∅ 0 n) 0 (n / 2))
    (addr' := 1) (eq_okVal hok2) (run_arg n) (eq_okVal hok1) hr1 (arrow1_eq hshape)
    (ThreadedAt.here_of_eq (eq_okVal hap) hm) rfl regC_get rfl (rd_ok _ n)
    (by simp [validateExternReturn, readRet, valueMatchesTyp])

/-! ## The cell -/

/-- The effect `!r` writes the cell at address 0, and the typing of the call
    stores `poisoned { 0 }` for it. -/
theorem cell_found (n : Int) : EffectCell (entryOf n) [rdEff] callRes "r" 0 cellQt := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, hlocs, hcell, _⟩ := hf
  unfold refLocs at hlocs
  split at hlocs
  · rename_i ls _ _ hlk
    simp only [Option.some.injEq] at hlocs
    exact EffectCell.mk (List.mem_singleton_self _) rfl hlk rfl hlocs (isCell_eq hcell)
      (by simp [entryOf, ExternCallEntry.ofRuntime, VarEnv.lookup, VarEnv.update])
  · cases hlocs

/-- The cell `!r` is the only cell the call writes. -/
private theorem cell_inv {n : Int} {v : Name} {addr : Address} {qt : QTyp}
    (h : EffectCell (entryOf n) [rdEff] callRes v addr qt) :
    v = "r" ∧ addr = 0 ∧ qt = cellQt := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, hlocs, hcell, _⟩ := hf
  cases h with
  | @mk ef _ qtv ls l _ _ hef htg hlk hety hls hmem hu =>
    rw [List.mem_singleton] at hef
    subst hef
    simp only [rdEff, EffectTarget.namedVar.injEq] at htg
    subst htg
    have hlk' : body.varEnv.lookup "r" = some qtv := hlk
    rw [hlk'] at hlocs
    obtain ⟨ety, pz, pr⟩ := qtv
    simp only at hety
    subst hety
    simp only [refLocs, Option.some.injEq] at hlocs
    rw [hlocs, List.cons.injEq] at hls
    obtain ⟨rfl, -⟩ := hls
    rw [isCell_eq hcell, Option.some.injEq] at hmem
    simp only [entryOf, ExternCallEntry.ofRuntime, VarEnv.lookup, VarEnv.update,
      List.lookup, beq_self_eq_true, Option.some.injEq, Value.loc.injEq] at hu
    exact ⟨rfl, hu.symm, hmem.symm⟩

/-! ## The premises -/

/-- A call agrees with itself: the same entry, the same final state and the
    same returned value. -/
theorem callAgrees_refl {entry : ExternCallEntry} {effects : List Effect} {res : TypeResult}
    {cf : Config} {o : Value} : CallAgrees entry entry effects res cf cf o o := by
  refine ⟨fun _ _ _ _ _ _ => rfl, ?_⟩
  intro v a₀ a₁ qt n₀ n₁ h₀ h₁ hn₀ hn₁ _ _ _ _
  rcases h₀ with ⟨_, _, _, _, _, _, hu₀⟩
  rcases h₁ with ⟨_, _, _, _, _, _, hu₁⟩
  rw [hu₀, Option.some.injEq, Value.loc.injEq] at hu₁
  subst hu₁
  rw [hn₀, Option.some.injEq] at hn₁
  exact hn₁

private theorem cfgF_cell (n : Int) : (cfgF n).memory.lookup 0 = some (n / 2) := by
  simp [cfgF, Memory.lookup, Memory.update]

/-- *Match* holds in every run: the call returns 0, which passes the check,
    and the guard of the cell has no predicate. -/
theorem match_of (n : Int) (predSat : PredSat)
    {β : BindVals} (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β) :
    ExternCallsMatch predSat (U0 n) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, ht, hreg, _, _, _, _, hd, _⟩ := hf
  refine ⟨fun s effects entry res cf o hreach hcall => ?_,
    fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hreach) hcall
  refine ⟨(callMatches_of (entry := entryOf n) (cf := cfgF n) hlaws hd ht hreg
    (by decide)).ret, ?_⟩
  intro v addr qt _ hc _ _ _ _ _ _ _ hpred _
  obtain ⟨-, -, rfl⟩ := cell_inv hc
  simp [cellQt] at hpred

/-- *Agreement* for the pair holds exactly when the two runs leave the same
    content in the cell. -/
theorem agree_iff (n₀ n₁ : Int) : ExternCallsAgree (U0 n₀) (U0 n₁) ↔ n₀ / 2 = n₁ / 2 := by
  constructor
  · intro h
    have hf := facts_ok
    simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
    obtain ⟨_, _, _, _, ht, hreg, _⟩ := hf
    have hag := h.calls _ _ _ _ _ _ _ _ _ _ (Reach.refl _) (Reach.refl _) rfl rfl rfl (call_mk n₀)
      (call_mk n₁) rfl
    have hmem : (0 : Tag) ∈ callRes.tagLog'.map (·.tag) := by rw [ht]; simp
    obtain ⟨a, ha, hat⟩ := List.mem_map.mp hmem
    exact hag.cells "r" 0 0 cellQt _ _ (cell_found n₀) (cell_found n₁) (cfgF_cell n₀)
      (cfgF_cell n₁) a ha (by rw [hat]; rfl) (by rw [hat]; exact hreg)
  · intro hn
    refine ⟨fun s₀ s₁ _ _ _ res _ _ o₀ o₁ hr₀ hr₁ _ _ _ hc₀ hc₁ _ => ?_⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := inSet_call (inSet_reach hr₀) hc₀
    obtain ⟨-, rfl, -, rfl, rfl⟩ := inSet_call (inSet_reach hr₁) hc₁
    refine ⟨fun _ _ _ _ _ _ => rfl, ?_⟩
    intro v a₀ a₁ qt m₀ m₁ h₀ h₁ hm₀ hm₁ _ _ _ _
    obtain ⟨-, rfl, -⟩ := cell_inv h₀
    obtain ⟨-, rfl, -⟩ := cell_inv h₁
    rw [cfgF_cell, Option.some.injEq] at hm₀ hm₁
    rw [← hm₀, ← hm₁, hn]

/-- **A cell written by an effect.** The typing accepts the program. In the
    run with `x = n`, the call writes `n / 2` to the cell at address 0; the
    typing of the call stores `poisoned { 0 }` for the cell, and the policy
    sets tag 0 true. *Match* holds in every run for every lawful `predSat`
    (and one exists). *Agreement* holds for the pair 4, 5, whose cells both
    hold 2 after the call, and fails for the pair 4, 6. -/
theorem cell_case :
    typecheck K0 prog 60 = .ok rootRes ∧
    (∀ n, ExternCallAt (U0 n) [rdEff] (entryOf n) callRes (cfgF n) (.num 0) ∧
      EffectCell (entryOf n) [rdEff] callRes "r" 0 cellQt ∧
      (cfgF n).memory.lookup 0 = some (n / 2)) ∧
    qtypGuardTag cellQt = some 0 ∧ callRes.regime'.lookup? 0 = some true ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ rootRes.tagLog') β →
        ∀ n, ExternCallsMatch predSat (U0 n)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ rootRes.tagLog') β) ∧
    ExternCallsAgree (U0 4) (U0 5) ∧
    ¬ ExternCallsAgree (U0 4) (U0 6) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, _, _, _, _, hreg, _, _, _, _, _, hall⟩ := hf
  refine ⟨eq_okVal hp, fun n => ⟨call_mk n, cell_found n, cfgF_cell n⟩, rfl, hreg,
    fun predSat _ hlaws n => match_of n predSat hlaws,
    fun _ => predSatLaws_geSat (geTable_of_allGe hall),
    (agree_iff 4 5).2 (by decide), ?_⟩
  rw [agree_iff]
  decide

/-! ## The guards the run tests -/

/-- The run reaches no conditional, so the condition on the guards it tests
    holds for every view. -/
theorem tests (n : Int) (β : BindVals) : TestsAgreeWithView β (U0 n) := by
  refine ⟨?_⟩
  intro ctx e1 e2 e3 f cfg _ _ _ _ hreach _ _ _
  have hs := inSet_reach hreach
  generalize hst : (⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ : Step) = st at hs
  exfalso
  cases hs with
  | leaf hl => subst hst; exact noAppIte_ne_ite hl rfl
  | _ => simp [U0, prog] at hst

end Cell

end ExternCallsWitness
