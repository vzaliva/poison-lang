import LeanProofs.ExternCallsWitnessBase

/-!
# Premises on extern calls for four programs

Programs over the extern `read` (the identity on integers, whose result
carries the guard `w => w >= 0`), each with the premises on extern calls
(`ExternCallsMatch`, `ExternCallsAgree`) proved or refuted.

* `Wrapper`: `let read = … in let f = fn u => read u in let a = f 1 in
  let b = f (0 - 3) in b`. One call site of `read`, executed twice through a
  wrapper. The typing allocates tag 0 for the first call and tag 1 for the
  second. *Match* holds when the policy sets tag 0 true and tag 1 false (the
  values the run computes, 1 and -3), and fails when it sets both true. It
  fails also when it sets every tag false, since the first call returns 1.
* `Skipped`: `let read = … in let a = read 1 in if a >= 0 then read (0 - 3)
  else read 4`. The taken branch calls and the skipped branch calls too. Tag 0
  is the call before the `if`, tag 1 the call in the taken branch and tag 2 the
  call in the skipped branch. *Match* holds for tag 0 true and tag 1 false
  whatever the policy sets for tag 2, and fails when all tags are true or when
  all tags are false.
* `TwoRuns`: `let read = … in read x` with `x` a poisoned input, in two runs.
  The call allocates tag 0, which the policy sets true. *Match* holds in runs
  with non-negative `x`; *agreement* holds exactly when the two runs start
  with the same `x`.
* `TwoCalls`: `let read = … in let a = read x in read y` with `x` and `y`
  poisoned inputs, in two runs. Each run makes two tagged calls (tags 0 and 1,
  both set true), which return `x` and `y`. *Agreement* pairs each call with
  the same call of the other run: it holds for the runs (5, 7) and (5, 7),
  where a crossed pairing would compare 5 with 7, and fails for (5, 7) and
  (5, 8).

For `Wrapper` and `Skipped`, *agreement* also holds for two copies of the
run under the vector it follows (`agree_self`).

For each program the computed typing facts are checked by the kernel
(`decide +kernel`), and the premises are proved for every `predSat` that
satisfies the laws on the program table. The relation `geSat` satisfies the
laws, so the laws can be met.
-/

open Std LeanPoison

namespace ExternCallsWitness

/-! ## Pieces shared by the programs -/

/-- The expression `0 - 3`. -/
def neg3 : Expr := Expr.op (Expr.num 0) Op.sub (Expr.num 3)

/-- The expression `x >= 0`. -/
def ge0 (x : Name) : Expr := Expr.op (Expr.var x) Op.gte (Expr.num 0)

private theorem run_neg3 (cfg : Config) : terminatesTo neg3 cfg cfg (.num (-3)) :=
  ⟨2, false, by simp [neg3, beval, evalOp]⟩

/-- The empty typing context with the extern policy `policy`. -/
def ctxWith (policy : ExternId → Tag → Option Bool) : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅, varEnv := ∅, tagEnv := ∅,
    nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := policy }

/-- *Match* fails at a reachable call that allocated the one tag `k`, whose
    regime entry `b` disagrees with the check on the returned value. -/
private theorem refute_gen {predSat : PredSat} {P : TagMeaning} {root s : Step}
    {effects : List Effect} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config} {k : Tag} {n : Int} {b : Bool}
    {β : BindVals} (hlaws : PredSatLaws predSat P β) (hd : descGe P k = true)
    (hreach : Reach root s) (hcall : ExternCallAt s effects entry res cf (.num n))
    (ht : res.tagLog'.map (·.tag) = [k]) (hg : guardAt res.qualType.pred k = true)
    (hr : res.regime'.lookup? k = some b) (hb : ¬ (0 ≤ n ↔ b = true)) :
    ¬ ExternCallsMatch predSat root := by
  intro hm
  have hcm := hm.calls _ _ _ _ _ _ hreach hcall
  obtain ⟨argName, body, cap, hpred⟩ := guardAt_spec hg
  have hmem : k ∈ res.tagLog'.map (·.tag) := by rw [ht]; simp
  obtain ⟨a, ha, hat⟩ := List.mem_map.mp hmem
  have h := hcm.ret a ha argName body cap b (by rw [hat]; exact hpred) (by rw [hat]; exact hr)
  rw [hat, pin hlaws hd] at h
  exact hb h

/-! ## A call site executed twice

`let read = … in let f = fn u => read u in let a = f 1 in let b = f (0 - 3) in b`

The run calls `read` with 1 and then with -3, both times from the body of `f`.
The one call site `read u` is typed once per call of `f`, against two
different member results, with tags 0 and 1. The vector the run follows is
tag 0 true, tag 1 false. *Match* holds for that vector and fails for the vector
true, true. -/

namespace Wrapper

def bodyF : Expr := .app (.var "read") (.var "u")
def fnF : Expr := .fn "u" Typ.int bodyF Typ.int
def A1 : Expr := .app (.var "f") (.num 1)
def A2 : Expr := .app (.var "f") neg3
def B3 : Expr := .vlet "b" A2 (.var "b")
def B2 : Expr := .vlet "a" A1 B3
def B1 : Expr := .vlet "f" fnF B2
def prog : Expr := .vlet "read" (readD false) B1

/-! ### Impure arrows with one member -/

private def isArrow1 : ETyp → Bool
  | .arrow _ _ _ [_] => true
  | _ => false

private def arrowS1 : ETyp → Typ
  | .arrow a _ _ _ => a
  | _ => Typ.int

private def arrowS2 : ETyp → Typ
  | .arrow _ b _ _ => b
  | _ => Typ.int

def arrowP : ETyp → Poison
  | .arrow _ _ p _ => p
  | _ => false

def arrowM : ETyp → FnTClosure
  | .arrow _ _ _ [m] => m
  | _ => .regular "" .unit []

private theorem arrow1_eq {E : ETyp} (h : isArrow1 E = true) :
    E = .arrow (arrowS1 E) (arrowS2 E) (arrowP E) [arrowM E] := by
  match E, h with
  | .arrow _ _ _ [_], _ => rfl

def regTenv : FnTClosure → CapturedVarEnv
  | .regular _ _ t => t
  | .extern _ _ _ _ _ _ _ => []

/-! ### The run -/

def cfg0 : Config :=
  { memory := ∅, varEnv := [], nextAddr := 0, pureMode := false, registry := reg }
def readV : Value := readClo false cfg0.varEnv
def cfg1 : Config := { cfg0 with varEnv := VarEnv.update cfg0.varEnv "read" readV }
def fClo : Value := .closure "u" bodyF cfg1.varEnv
def cfg2 : Config := { cfg1 with varEnv := VarEnv.update cfg1.varEnv "f" fClo }
def cfg3 : Config := { cfg2 with varEnv := VarEnv.update cfg2.varEnv "a" (.num 1) }

/-- The configuration of the body of `f` for a call from `cfg` with argument `n`. -/
def wBodyCfg (cfg : Config) (n : Int) : Config :=
  { { cfg with varEnv := cfg.varEnv } with
    varEnv := VarEnv.update cfg1.varEnv "u" (.num n), pureMode := false }

private theorem run_fnF : terminatesTo fnF cfg1 cfg1 fClo :=
  ⟨1, false, by unfold beval; simp [fnF, fClo]⟩

private theorem run_A1 : terminatesTo A1 cfg2 cfg2 (.num 1) :=
  ⟨10, false, by
    simp [beval, bevalFunctionBody, A1, cfg2, cfg1, cfg0, fClo, readV, readClo, readD, readRet,
      bodyF, VarEnv.lookup, VarEnv.update, reg_get', validateExternReturn, valueMatchesTyp,
      idImpl, List.lookup]⟩

private theorem runF (cfg : Config) (h : cfg.varEnv.lookup "f" = some fClo) :
    ∀ c, c.varEnv = cfg.varEnv → terminatesTo (.var "f") c c fClo := by
  intro c hc
  exact run_var (by rw [hc]; exact h)

private theorem runRead (n : Int) (cfg : Config) :
    ∀ c, c.varEnv = (wBodyCfg cfg n).varEnv →
      terminatesTo (.var "read") c c (readClo false cfg0.varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; rfl)

private theorem runU (n : Int) (cfg : Config) :
    terminatesTo (.var "u") (wBodyCfg cfg n) (wBodyCfg cfg n) (.num n) :=
  run_var rfl

/-! ### The call of the wrapper -/

/-- The body context of the wrapper member, for the call `f arg` whose parts
    are typed at fuel `G`. -/
def wBody (C : TypeContext) (arg : Expr) (G : Nat) : TypeContext :=
  let E := (iFun C (.var "f") arg G).qualType.etyp
  fnBodyCtx C (iArg C arg G) (iFun C (.var "f") arg G) (arrowP E) "u" (regTenv (arrowM E))
    (iCursor C (.var "f") arg G) (iBind C (.var "f") arg G)

/-- The parts of the call `f arg`: the argument, the function, or the body of
    the wrapper. -/
private theorem wrap_sub {C : TypeContext} {arg : Expr} {H : Nat} {cfg : Config} {n : Int}
    (hrunF : ∀ c, c.varEnv = cfg.varEnv → terminatesTo (.var "f") c c fClo)
    (hrunA : terminatesTo arg cfg cfg (.num n))
    (harg : noAppIte arg = true)
    (hok2 : isOkB (typecheckExpr C arg (H + 1)) = true)
    (hok1 : isOkB (typecheckExpr (ctxAfter C (iArg C arg (H + 1))) (.var "f") (H + 1)) = true)
    (hshape : isArrow1 (iFun C (.var "f") arg (H + 1)).qualType.etyp = true)
    {s' : Step} (h : SubStep ⟨C, .app (.var "f") arg, H + 3, cfg⟩ s') :
    noAppIte s'.e = true ∨ s' = ⟨wBody C arg (H + 1), bodyF, H, wBodyCfg cfg n⟩ := by
  have hh := SubStep.app_inv h
  clear h
  obtain ⟨G, hG, h⟩ := hh
  obtain rfl : H + 1 = G := by omega
  rcases h with h | h | h | h
  · subst h; exact Or.inl harg
  · obtain ⟨_, _, _, _, _, rfl⟩ := h; exact Or.inl rfl
  · obtain ⟨H', r2, r1, rb, c2, c1, v2, x, body, env', st1, st2, p, tcls, tenv, cursor, bn,
      hH, h2, hr2, h1, hr1, hety, hthr, rfl⟩ := h
    obtain rfl : H = H' := by omega
    obtain rfl : r2 = iArg C arg (H + 1) := ok_inj h2 (eq_okVal hok2)
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    obtain rfl : r1 = iFun C (.var "f") arg (H + 1) := ok_inj h1 (eq_okVal hok1)
    obtain ⟨hc1, hv⟩ := terminatesTo_det hr1 (hrunF _ rfl)
    subst c1
    simp only [fClo, Value.closure.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    rw [arrow1_eq hshape] at hety
    simp only [ETyp.arrow.injEq] at hety
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hety
    obtain ⟨hm, rfl, rfl, _⟩ := ThreadedAt.single_inv hthr
    refine Or.inr ?_
    simp only [wBody, wBodyCfg, ← hm, regTenv]
    rfl
  · obtain ⟨H', r2, r1, rb, c2, c1, v2, x, body, pbody, env', st1, st2, p, tcls, tenv, cursor, bn,
      hH, h2, hr2, h1, hr1, _⟩ := h
    obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    have := terminatesTo_det hr1 (hrunF _ rfl)
    simp [fClo] at this

/-- The call `f arg` makes no extern call itself: `f` evaluates to a wrapper. -/
private theorem wrap_call {C : TypeContext} {arg : Expr} {H : Nat} {cfg : Config} {n : Int}
    (hrunF : ∀ c, c.varEnv = cfg.varEnv → terminatesTo (.var "f") c c fClo)
    (hrunA : terminatesTo arg cfg cfg (.num n))
    {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult} {cf : Config}
    {o : Value}
    (h : ExternCallAt ⟨C, .app (.var "f") arg, H + 3, cfg⟩ effects entry res cf o) : False := by
  have hh := ExternCallAt.app_inv h
  clear h
  obtain ⟨G, _, h⟩ := hh
  rcases h with
    ⟨r2, r1, c2, c1, v2, vRaw, x, y, env', id, argTyp, argPoison, argPred, retSpec, captures,
      memberCaptures, st1, st2, p, tcls, tenv, declaredArgQt, cursor, bn, implFn,
      _, hr2, _, hr1, _⟩ |
    ⟨r2, r1, c2, c1, v2, x, y, env', id, argTyp, argPoison, argPred, retSpec, effs, captures,
      _, hr2, _, hr1⟩
  · obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    have := terminatesTo_det hr1 (hrunF _ rfl)
    simp [fClo] at this
  · obtain ⟨hc2, rfl⟩ := terminatesTo_det hr2 hrunA
    subst c2
    have := terminatesTo_det hr1 (hrunF _ rfl)
    simp [fClo, bodyF] at this

/-! ### Typing, for a policy `pol` -/

def C0 (pol : ExternId → Tag → Option Bool) : TypeContext := ctxWith pol
def r0 (pol : ExternId → Tag → Option Bool) : TypeResult :=
  okVal (typecheckExpr (C0 pol) (readD false) 58)
def C1 (pol : ExternId → Tag → Option Bool) : TypeContext :=
  { ctxAfter (C0 pol) (r0 pol) with
    varEnv := (C0 pol).varEnv.update "read" (r0 pol).qualType,
    bindEnv := (C0 pol).bindEnv.insert "read" (r0 pol).nextBind',
    nextBind := (r0 pol).nextBind' + 1 }
def rF (pol : ExternId → Tag → Option Bool) : TypeResult := okVal (typecheckExpr (C1 pol) fnF 56)
def C2 (pol : ExternId → Tag → Option Bool) : TypeContext :=
  { ctxAfter (C1 pol) (rF pol) with
    varEnv := (C1 pol).varEnv.update "f" (rF pol).qualType,
    bindEnv := (C1 pol).bindEnv.insert "f" (rF pol).nextBind',
    nextBind := (rF pol).nextBind' + 1 }
def rA (pol : ExternId → Tag → Option Bool) : TypeResult := okVal (typecheckExpr (C2 pol) A1 54)
def C3 (pol : ExternId → Tag → Option Bool) : TypeContext :=
  { ctxAfter (C2 pol) (rA pol) with
    varEnv := (C2 pol).varEnv.update "a" (rA pol).qualType,
    bindEnv := (C2 pol).bindEnv.insert "a" (rA pol).nextBind',
    nextBind := (rA pol).nextBind' + 1 }

def rootRes (pol : ExternId → Tag → Option Bool) : TypeResult :=
  okVal (typecheckExpr (C0 pol) prog 60)

/-- The bodies of the two calls of `f`. -/
def BA (pol : ExternId → Tag → Option Bool) : TypeContext := wBody (C2 pol) (.num 1) 52
def BB (pol : ExternId → Tag → Option Bool) : TypeContext := wBody (C3 pol) neg3 50

def S0 (pol : ExternId → Tag → Option Bool) : Step := ⟨C0 pol, prog, 60, cfg0⟩
private def S2 (pol : ExternId → Tag → Option Bool) : Step := ⟨C1 pol, B1, 58, cfg1⟩
private def S4 (pol : ExternId → Tag → Option Bool) : Step := ⟨C2 pol, B2, 56, cfg2⟩
private def S5 (pol : ExternId → Tag → Option Bool) : Step := ⟨C2 pol, A1, 54, cfg2⟩
private def S6 (pol : ExternId → Tag → Option Bool) : Step := ⟨C3 pol, B3, 54, cfg3⟩
private def S10 (pol : ExternId → Tag → Option Bool) : Step := ⟨C3 pol, A2, 52, cfg3⟩
def S9 (pol : ExternId → Tag → Option Bool) : Step := ⟨BA pol, bodyF, 51, wBodyCfg cfg2 1⟩
def S13 (pol : ExternId → Tag → Option Bool) : Step :=
  ⟨BB pol, bodyF, 49, wBodyCfg cfg3 (-3)⟩

/-- The vector the run follows: the first call (tag 0) returns 1, the second
    (tag 1) returns -3. -/
def real : ExternId → Tag → Option Bool := on7 (· == 0)

/-- Both calls committed true. -/
def bad : ExternId → Tag → Option Bool := on7 fun _ => true

/-- Every tag false. -/
def allF : ExternId → Tag → Option Bool := on7 fun _ => false

/-! ### The typing facts, computed by the kernel -/

section Facts
variable (pol : ExternId → Tag → Option Bool)

/-- What the proofs need from the typing under `pol`. -/
private def facts : Bool :=
  isOkB (typecheckExpr (C0 pol) prog 60) &&
  isOkB (typecheckExpr (C0 pol) (readD false) 58) &&
  isOkB (typecheckExpr (C1 pol) fnF 56) &&
  isOkB (typecheckExpr (C2 pol) A1 54) &&
  isOkB (typecheckExpr (C3 pol) A2 52) &&
  isOkB (typecheckExpr (C2 pol) (.num 1) 52) &&
  isOkB (typecheckExpr (ctxAfter (C2 pol) (iArg (C2 pol) (.num 1) 52)) (.var "f") 52) &&
  isArrow1 (iFun (C2 pol) (.var "f") (.num 1) 52).qualType.etyp &&
  isOkB (typecheckExpr (C3 pol) neg3 50) &&
  isOkB (typecheckExpr (ctxAfter (C3 pol) (iArg (C3 pol) neg3 50)) (.var "f") 50) &&
  isArrow1 (iFun (C3 pol) (.var "f") neg3 50).qualType.etyp &&
  isOkB (typecheckExpr (BA pol) (.var "u") 49) &&
  isOkB (typecheckExpr (ctxAfter (BA pol) (iArg (BA pol) (.var "u") 49)) (.var "read") 49) &&
  isParrow1 (iFun (BA pol) (.var "read") (.var "u") 49).qualType.etyp &&
  isOkB (typecheckExpr (BB pol) (.var "u") 47) &&
  isOkB (typecheckExpr (ctxAfter (BB pol) (iArg (BB pol) (.var "u") 47)) (.var "read") 47) &&
  isParrow1 (iFun (BB pol) (.var "read") (.var "u") 47).qualType.etyp &&
  ((iRes (BA pol) (.var "read") (.var "u") 49).tagLog'.map (·.tag) == [0]) &&
  ((iRes (BB pol) (.var "read") (.var "u") 47).tagLog'.map (·.tag) == [1]) &&
  descGe (programTable ∅ (rootRes pol).tagLog') 0 &&
  descGe (programTable ∅ (rootRes pol).tagLog') 1 &&
  allGe (rootRes pol).tagLog'

end Facts

private theorem facts_real : facts real = true := by decide +kernel
private theorem facts_bad : facts bad = true := by decide +kernel
private theorem facts_allF : facts allF = true := by decide +kernel

/-- The member of `read`'s type: its extern member, with no captured variables. -/
private def readMemberOk : PFnTClosure → Bool
  | .extern i x r [] _ _ => i == 7 && x == "b" && r == readRet
  | _ => false

/-- The captured environment of the wrapper's member: `read` alone, at a pure
    function type over `int` with `read`'s extern member. -/
private def tenvReadOk : CapturedVarEnv → Bool
  | [(y, ⟨.parrow a r _ tcl, _, _⟩, _)] =>
      y == "read" && a == Typ.int && r == parseReturnType readRet && tcl.any readMemberOk
  | _ => false

/-- The wrapper's closure environment is typed by a captured environment that
    passes `tenvReadOk`. -/
private theorem typing_of_tenvReadOk {tenv : CapturedVarEnv} (h : tenvReadOk tenv = true) :
    ∃ θ, capturedVarsTypingProperty θ tenv cfg1.varEnv := by
  refine ⟨∅, ?_⟩
  match tenv, h with
  | [(y, ⟨.parrow a r p tcl, ps, pr⟩, n)], h =>
    simp only [tenvReadOk, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, m, hm, hmok⟩ := h
    match m, hmok with
    | .extern i x rr [] aq c, hmok =>
      simp only [readMemberOk, Bool.and_eq_true, beq_iff_eq] at hmok
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hmok
      refine ⟨by simp, fun z qt hz => ?_, fun z qt v hz hv => ?_⟩
      · simp only [CapturedVarEnv.lookup, List.lookup] at hz
        split at hz
        · rename_i heq
          have : z = "read" := beq_iff_eq.mp heq
          subst this
          exact ⟨readV, by simp [cfg1, cfg0, VarEnv.update, VarEnv.lookup]⟩
        · simp at hz
      · simp only [CapturedVarEnv.lookup, List.lookup] at hz
        split at hz
        · rename_i heq
          have : z = "read" := beq_iff_eq.mp heq
          subst this
          simp only [Option.map_some, Option.some.injEq] at hz
          subst hz
          have hv' : v = readV := by
            simpa [cfg1, cfg0, VarEnv.update, VarEnv.lookup] using hv.symm
          subst hv'
          exact valueHasETyp.peClosure_extern (htcl := hm)
            (henv := fun _ _ _ h _ => by simp [CapturedVarEnv.lookup] at h)
            (hcover := fun _ _ h => by simp [CapturedVarEnv.lookup] at h)
        · simp at hz

private theorem tenvA_real :
    tenvReadOk (regTenv (arrowM (iFun (C2 real) (.var "f") (.num 1) 52).qualType.etyp)) = true := by
  decide +kernel
private theorem tenvA_allF :
    tenvReadOk (regTenv (arrowM (iFun (C2 allF) (.var "f") (.num 1) 52).qualType.etyp)) = true := by
  decide +kernel
private theorem tenvB_real :
    tenvReadOk (regTenv (arrowM (iFun (C3 real) (.var "f") neg3 50).qualType.etyp)) = true := by
  decide +kernel
private theorem tenvB_bad :
    tenvReadOk (regTenv (arrowM (iFun (C3 bad) (.var "f") neg3 50).qualType.etyp)) = true := by
  decide +kernel


private theorem regime_real :
    (iRes (BA real) (.var "read") (.var "u") 49).regime'.lookup? 0 = some true ∧
    (iRes (BB real) (.var "read") (.var "u") 47).regime'.lookup? 1 = some false := by
  decide +kernel

private theorem regime_bad :
    (iRes (BB bad) (.var "read") (.var "u") 47).regime'.lookup? 1 = some true := by
  decide +kernel

private theorem regime_allF :
    (iRes (BA allF) (.var "read") (.var "u") 49).regime'.lookup? 0 = some false := by
  decide +kernel

/-! ### The steps the run reaches -/

private inductive InSet (pol : ExternId → Tag → Option Bool) : Step → Prop
  | s0 : InSet pol (S0 pol)
  | s2 : InSet pol (S2 pol)
  | s4 : InSet pol (S4 pol)
  | s5 : InSet pol (S5 pol)
  | s6 : InSet pol (S6 pol)
  | s9 : InSet pol (S9 pol)
  | s10 : InSet pol (S10 pol)
  | s13 : InSet pol (S13 pol)
  | leaf {s : Step} : noAppIte s.e = true → InSet pol s

private theorem inSet_step {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    {s s' : Step} (hs : InSet pol s) (h : SubStep s s') : InSet pol s' := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, h0, hF, hA1, _, hn1, hf1, ha1, hn3, hf3, ha3, _⟩ := hf
  cases hs with
  | s0 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := C0 pol) (x := "read") (e1 := readD false)
        (e2 := B1) (F := 60) (cfg := cfg0) h
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl : r1 = r0 pol := ok_inj h1 (eq_okVal h0)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 (run_readD false cfg0 rfl)
        exact InSet.s2
  | s2 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := C1 pol) (x := "f") (e1 := fnF)
        (e2 := B2) (F := 58) (cfg := cfg1) h
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl : r1 = rF pol := ok_inj h1 (eq_okVal hF)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 run_fnF
        exact InSet.s4
  | s4 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := C2 pol) (x := "a") (e1 := A1)
        (e2 := B3) (F := 56) (cfg := cfg2) h
      obtain rfl : f = 54 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.s5
      · obtain rfl : r1 = rA pol := ok_inj h1 (eq_okVal hA1)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 run_A1
        exact InSet.s6
  | s6 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := C3 pol) (x := "b") (e1 := A2)
        (e2 := .var "b") (F := 54) (cfg := cfg3) h
      obtain rfl : f = 52 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.s10
      · exact InSet.leaf rfl
  | s5 =>
      rcases wrap_sub (C := C2 pol) (arg := .num 1) (H := 51) (cfg := cfg2) (n := 1)
          (runF cfg2 rfl) (run_num _ _) rfl hn1 hf1 ha1 h with hl | rfl
      · exact InSet.leaf hl
      · exact InSet.s9
  | s10 =>
      rcases wrap_sub (C := C3 pol) (arg := neg3) (H := 49) (cfg := cfg3) (n := -3)
          (runF cfg3 rfl) (run_neg3 _) rfl hn3 hf3 ha3 h with hl | rfl
      · exact InSet.leaf hl
      · exact InSet.s13
  | s9 =>
      exact InSet.leaf (readCall_sub (B := BA pol) (fe := .var "read") (arg := .var "u")
        (F := 51) (cfgB := wBodyCfg cfg2 1) rfl rfl (runRead 1 cfg2) (runU 1 cfg2) h)
  | s13 =>
      exact InSet.leaf (readCall_sub (B := BB pol) (fe := .var "read") (arg := .var "u")
        (F := 49) (cfgB := wBodyCfg cfg3 (-3)) rfl rfl (runRead (-3) cfg3) (runU (-3) cfg3) h)
  | leaf hl => exact InSet.leaf (SubStep.noAppIte h hl)

private theorem inSet_reach {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    {s : Step} (h : Reach (S0 pol) s) : InSet pol s := by
  induction h with
  | refl => exact InSet.s0
  | tail _ hsub ih => exact inSet_step hf ih hsub

/-- The two calls the run makes. -/
private theorem inSet_call {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    {s : Step} {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {o : Value}
    (hs : InSet pol s) (h : ExternCallAt s effects entry res cf o) :
    (res = iRes (BA pol) (.var "read") (.var "u") 49 ∧ o = .num 1 ∧ effects = []) ∨
    (res = iRes (BB pol) (.var "read") (.var "u") 47 ∧ o = .num (-3) ∧ effects = []) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hu9, hr9, hp9, hu13, hr13, hp13, _⟩ := hf
  cases hs with
  | s0 => cases h
  | s2 => cases h
  | s4 => cases h
  | s6 => cases h
  | s5 => exact (wrap_call (C := C2 pol) (arg := .num 1) (H := 51) (cfg := cfg2) (n := 1)
      (runF cfg2 rfl) (run_num _ _) h).elim
  | s10 => exact (wrap_call (C := C3 pol) (arg := neg3) (H := 49) (cfg := cfg3) (n := -3)
      (runF cfg3 rfl) (run_neg3 _) h).elim
  | s9 =>
      obtain ⟨rfl, rfl, _, rfl, _⟩ := readCall_call (B := BA pol) (fe := .var "read")
        (arg := .var "u") (G := 49) (cfgB := wBodyCfg cfg2 1) (runRead 1 cfg2) (runU 1 cfg2) rfl
        hu9 hr9 hp9 h
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | s13 =>
      obtain ⟨rfl, rfl, _, rfl, _⟩ := readCall_call (B := BB pol) (fe := .var "read")
        (arg := .var "u") (G := 47) (cfgB := wBodyCfg cfg3 (-3)) (runRead (-3) cfg3)
        (runU (-3) cfg3) rfl hu13 hr13 hp13 h
      exact Or.inr ⟨rfl, rfl, rfl⟩
  | leaf hl =>
      exact absurd h (ExternCallAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _))

/-- No step of the set declares an `extern val`. -/
private theorem inSet_val {pol : ExternId → Tag → Option Bool} {s : Step} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet pol s) :
    ¬ ExternValAt s res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternValAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _) h
  | _ => cases h

/-- **The premise holds for the vector the run follows** (tag 0 true, tag 1
    false), for every `predSat` lawful on the program table; and such a
    `predSat` exists. -/
theorem prog_real :
    typecheck (C0 real) prog 60 = .ok (rootRes real) ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ (rootRes real).tagLog') β →
      ExternCallsMatch predSat (S0 real)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ (rootRes real).tagLog') β) := by
  have hf := facts_real
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht9, ht13, hd0, hd1, hall⟩ := hf
  refine ⟨eq_okVal hp, ?_, fun _ => predSatLaws_geSat (geTable_of_allGe hall)⟩
  intro predSat _ hlaws
  refine ⟨fun s effects entry res cf o hreach hcall => ?_,
    fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach facts_real hreach))⟩
  rcases inSet_call facts_real (inSet_reach facts_real hreach) hcall with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact callMatches_of hlaws hd0 ht9 regime_real.1 (by decide)
  · exact callMatches_of hlaws hd1 ht13 regime_real.2 (by decide)

/-- *Agreement* holds for two copies of the run under the vector it follows:
    its two calls have different member results. -/
theorem agree_self : ExternCallsAgree (S0 real) (S0 real) := by
  have hf := facts_real
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht9, ht13, _⟩ := hf
  have hne := ne_of_tags ht9 ht13 (by decide)
  refine agree_self_of fun s₀ s₁ _ _ _ res _ _ o₀ o₁ hr₀ hr₁ hc₀ hc₁ => ?_
  rcases inSet_call facts_real (inSet_reach facts_real hr₀) hc₀ with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases inSet_call facts_real (inSet_reach facts_real hr₁) hc₁ with ⟨h, rfl, -⟩ | ⟨h, rfl, -⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd h hne
  · exact absurd h.symm hne
  · exact ⟨rfl, rfl⟩

/-! ### The vector true, true -/

private theorem facts_bad_chain :
    let E := (iFun (C3 bad) (.var "f") neg3 50).qualType.etyp
    let E' := (iFun (BB bad) (.var "read") (.var "u") 47).qualType.etyp
    arrowM E = .regular "u" bodyF (regTenv (arrowM E)) ∧
    isOkB (fnApply (C3 bad) (iArg (C3 bad) neg3 50) (iFun (C3 bad) (.var "f") neg3 50)
      (arrowS1 E) (arrowS2 E) (arrowP E) 50 (arrowM E) (iCursor (C3 bad) (.var "f") neg3 50)
        (iBind (C3 bad) (.var "f") neg3 50))
      = true ∧
    parrowM E' = .extern 7 "b" readRet (extParts (parrowM E')).1 (extParts (parrowM E')).2.1
      (extParts (parrowM E')).2.2 ∧
    isOkB (pfnApply (BB bad) (iArg (BB bad) (.var "u") 47)
      (iFun (BB bad) (.var "read") (.var "u") 47)
      (parrowS1 E') (parrowS2 E') (parrowP E') 47 (parrowM E')
      (iCursor (BB bad) (.var "read") (.var "u") 47)
        (iBind (BB bad) (.var "read") (.var "u") 47)) = true ∧
    guardAt (iRes (BB bad) (.var "read") (.var "u") 47).qualType.pred 1 = true := by
  decide +kernel

/-- The run reaches the second call. -/
private theorem reach_bad : Reach (S0 bad) (S13 bad) := by
  have hf := facts_bad
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, h0, hF, hA1, _, _, _, _, hn3, hf3, ha3, _⟩ := hf
  obtain ⟨hm, hap, _⟩ := facts_bad_chain
  have e1 : SubStep (S0 bad) (S2 bad) :=
    SubStep.vletBody (c1 := cfg0) (v1 := readV) (eq_okVal h0) (run_readD false cfg0 rfl)
  have e2 : SubStep (S2 bad) (S4 bad) :=
    SubStep.vletBody (c1 := cfg1) (v1 := fClo) (eq_okVal hF) run_fnF
  have e3 : SubStep (S4 bad) (S6 bad) :=
    SubStep.vletBody (c1 := cfg2) (v1 := .num 1) (eq_okVal hA1) run_A1
  have e4 : SubStep (S6 bad) (S10 bad) := SubStep.vletBound
  have e5 : SubStep (S10 bad) (S13 bad) :=
    SubStep.appFnBody (H := 49) (c2 := cfg3) (v2 := .num (-3))
      (c1 := { cfg3 with varEnv := cfg3.varEnv })
      (eq_okVal hn3) (run_neg3 cfg3) (eq_okVal hf3) (runF cfg3 rfl _ rfl) (arrow1_eq ha3)
      (ThreadedAt.here_of_eq (eq_okVal hap) hm) (typing_of_tenvReadOk tenvB_bad)
  exact .tail (.tail (.tail (.tail (.tail .refl e1) e2) e3) e4) e5

/-- At the second call, `read` returns -3. -/
private theorem call_bad : ∃ entry,
    ExternCallAt (S13 bad) [] entry (iRes (BB bad) (.var "read") (.var "u") 47)
      (wBodyCfg cfg3 (-3)) (.num (-3)) := by
  have hf := facts_bad
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hu13, hr13, hp13, _⟩ := hf
  obtain ⟨_, _, hm', hap', _⟩ := facts_bad_chain
  obtain ⟨entry, -, h⟩ := readCall_mk (B := BB bad) (fe := .var "read") (arg := .var "u")
    (G := 47) (cfgB := wBodyCfg cfg3 (-3)) (runRead (-3) cfg3) (runU (-3) cfg3) rfl hu13 hr13
    hp13 hm' hap'
  exact ⟨entry, h⟩

/-- **The premise fails for the vector true, true**, for every `predSat` lawful
    on the program table; such a `predSat` exists. -/
theorem prog_bad :
    typecheck (C0 bad) prog 60 = .ok (rootRes bad) ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ (rootRes bad).tagLog') β →
      ¬ ExternCallsMatch predSat (S0 bad)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ (rootRes bad).tagLog') β) := by
  have hf := facts_bad
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht13, _, hd1, hall⟩ := hf
  refine ⟨eq_okVal hp, ?_, fun _ => predSatLaws_geSat (geTable_of_allGe hall)⟩
  intro predSat _ hlaws
  obtain ⟨entry, hcall⟩ := call_bad
  obtain ⟨_, _, _, _, hg⟩ := facts_bad_chain
  exact refute_of hlaws hd1 reach_bad hcall ht13 hg regime_bad (by decide)

/-! ### Both calls are reached, and the first tag is read

Under the vector the run follows, each of the two calls is reached and returns
the value the run computes, and its result carries a guard closure at the
call's tag, so *match* does constrain it. The premise also reads tag 0: with
every tag false it fails at the first call, which returns 1. -/

/-- The member results and guards of the two calls of `read` (through the
    wrapper `f`). -/
private def Chain (pol : ExternId → Tag → Option Bool) : Prop :=
  let E1 := (iFun (C2 pol) (.var "f") (.num 1) 52).qualType.etyp
  let E1' := (iFun (BA pol) (.var "read") (.var "u") 49).qualType.etyp
  let E2 := (iFun (C3 pol) (.var "f") neg3 50).qualType.etyp
  let E2' := (iFun (BB pol) (.var "read") (.var "u") 47).qualType.etyp
  arrowM E1 = .regular "u" bodyF (regTenv (arrowM E1)) ∧
  isOkB (fnApply (C2 pol) (iArg (C2 pol) (.num 1) 52) (iFun (C2 pol) (.var "f") (.num 1) 52)
    (arrowS1 E1) (arrowS2 E1) (arrowP E1) 52 (arrowM E1)
    (iCursor (C2 pol) (.var "f") (.num 1) 52) (iBind (C2 pol) (.var "f") (.num 1) 52)) = true ∧
  parrowM E1' = .extern 7 "b" readRet (extParts (parrowM E1')).1 (extParts (parrowM E1')).2.1
    (extParts (parrowM E1')).2.2 ∧
  isOkB (pfnApply (BA pol) (iArg (BA pol) (.var "u") 49)
    (iFun (BA pol) (.var "read") (.var "u") 49)
    (parrowS1 E1') (parrowS2 E1') (parrowP E1') 49 (parrowM E1')
    (iCursor (BA pol) (.var "read") (.var "u") 49)
      (iBind (BA pol) (.var "read") (.var "u") 49)) = true ∧
  guardAt (iRes (BA pol) (.var "read") (.var "u") 49).qualType.pred 0 = true ∧
  arrowM E2 = .regular "u" bodyF (regTenv (arrowM E2)) ∧
  isOkB (fnApply (C3 pol) (iArg (C3 pol) neg3 50) (iFun (C3 pol) (.var "f") neg3 50)
    (arrowS1 E2) (arrowS2 E2) (arrowP E2) 50 (arrowM E2)
    (iCursor (C3 pol) (.var "f") neg3 50) (iBind (C3 pol) (.var "f") neg3 50)) = true ∧
  parrowM E2' = .extern 7 "b" readRet (extParts (parrowM E2')).1 (extParts (parrowM E2')).2.1
    (extParts (parrowM E2')).2.2 ∧
  isOkB (pfnApply (BB pol) (iArg (BB pol) (.var "u") 47)
    (iFun (BB pol) (.var "read") (.var "u") 47)
    (parrowS1 E2') (parrowS2 E2') (parrowP E2') 47 (parrowM E2')
    (iCursor (BB pol) (.var "read") (.var "u") 47)
      (iBind (BB pol) (.var "read") (.var "u") 47)) = true ∧
  guardAt (iRes (BB pol) (.var "read") (.var "u") 47).qualType.pred 1 = true

private theorem chain_real : Chain real := by unfold Chain; decide +kernel
private theorem chain_allF : Chain allF := by unfold Chain; decide +kernel

/-- The run reaches the first call (inside the wrapper, applied to 1). -/
private theorem reachA {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (hc : Chain pol)
    (ht : tenvReadOk (regTenv (arrowM (iFun (C2 pol) (.var "f") (.num 1) 52).qualType.etyp))
      = true) :
    Reach (S0 pol) (S9 pol) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, h0, hF, _, _, hn1, hf1, ha1, _⟩ := hf
  obtain ⟨hm, hap, _⟩ := hc
  have e1 : SubStep (S0 pol) (S2 pol) :=
    SubStep.vletBody (c1 := cfg0) (v1 := readV) (eq_okVal h0) (run_readD false cfg0 rfl)
  have e2 : SubStep (S2 pol) (S4 pol) :=
    SubStep.vletBody (c1 := cfg1) (v1 := fClo) (eq_okVal hF) run_fnF
  have e3 : SubStep (S4 pol) (S5 pol) := SubStep.vletBound
  have e4 : SubStep (S5 pol) (S9 pol) :=
    SubStep.appFnBody (H := 51) (c2 := cfg2) (v2 := .num 1)
      (c1 := { cfg2 with varEnv := cfg2.varEnv })
      (eq_okVal hn1) (run_num cfg2 1) (eq_okVal hf1) (runF cfg2 rfl _ rfl) (arrow1_eq ha1)
      (ThreadedAt.here_of_eq (eq_okVal hap) hm) (typing_of_tenvReadOk ht)
  exact .tail (.tail (.tail (.tail .refl e1) e2) e3) e4

private theorem callA {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (hc : Chain pol) :
    ∃ entry cf,
      ExternCallAt (S9 pol) [] entry (iRes (BA pol) (.var "read") (.var "u") 49) cf (.num 1) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hu9, hr9, hp9, _⟩ := hf
  obtain ⟨_, _, hm', hap', _⟩ := hc
  obtain ⟨entry, -, h⟩ := readCall_mk (B := BA pol) (fe := .var "read") (arg := .var "u")
    (G := 49) (cfgB := wBodyCfg cfg2 1) (runRead 1 cfg2) (runU 1 cfg2) rfl hu9 hr9 hp9 hm' hap'
  exact ⟨entry, _, h⟩

/-- The run reaches the second call (inside the wrapper, applied to -3). -/
private theorem reachB {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (hc : Chain pol)
    (ht : tenvReadOk (regTenv (arrowM (iFun (C3 pol) (.var "f") neg3 50).qualType.etyp)) = true) :
    Reach (S0 pol) (S13 pol) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, h0, hF, hA1, _, _, _, _, hn3, hf3, ha3, _⟩ := hf
  obtain ⟨_, _, _, _, _, hm, hap, _⟩ := hc
  have e1 : SubStep (S0 pol) (S2 pol) :=
    SubStep.vletBody (c1 := cfg0) (v1 := readV) (eq_okVal h0) (run_readD false cfg0 rfl)
  have e2 : SubStep (S2 pol) (S4 pol) :=
    SubStep.vletBody (c1 := cfg1) (v1 := fClo) (eq_okVal hF) run_fnF
  have e3 : SubStep (S4 pol) (S6 pol) :=
    SubStep.vletBody (c1 := cfg2) (v1 := .num 1) (eq_okVal hA1) run_A1
  have e4 : SubStep (S6 pol) (S10 pol) := SubStep.vletBound
  have e5 : SubStep (S10 pol) (S13 pol) :=
    SubStep.appFnBody (H := 49) (c2 := cfg3) (v2 := .num (-3))
      (c1 := { cfg3 with varEnv := cfg3.varEnv })
      (eq_okVal hn3) (run_neg3 cfg3) (eq_okVal hf3) (runF cfg3 rfl _ rfl) (arrow1_eq ha3)
      (ThreadedAt.here_of_eq (eq_okVal hap) hm) (typing_of_tenvReadOk ht)
  exact .tail (.tail (.tail (.tail (.tail .refl e1) e2) e3) e4) e5

private theorem callB {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (hc : Chain pol) :
    ∃ entry cf,
      ExternCallAt (S13 pol) [] entry (iRes (BB pol) (.var "read") (.var "u") 47) cf
        (.num (-3)) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hu13, hr13, hp13, _⟩ := hf
  obtain ⟨_, _, _, _, _, _, _, hm', hap', _⟩ := hc
  obtain ⟨entry, -, h⟩ := readCall_mk (B := BB pol) (fe := .var "read") (arg := .var "u")
    (G := 47) (cfgB := wBodyCfg cfg3 (-3)) (runRead (-3) cfg3) (runU (-3) cfg3) rfl hu13 hr13
    hp13 hm' hap'
  exact ⟨entry, _, h⟩

/-- **Under the vector the run follows both calls are reached**, return 1 and
    -3, and carry guard closures at tags 0 and 1: `prog_real` constrains both. -/
theorem prog_live :
    (Reach (S0 real) (S9 real) ∧ ∃ entry cf,
      ExternCallAt (S9 real) [] entry (iRes (BA real) (.var "read") (.var "u") 49) cf
        (.num 1)) ∧
    (Reach (S0 real) (S13 real) ∧ ∃ entry cf,
      ExternCallAt (S13 real) [] entry (iRes (BB real) (.var "read") (.var "u") 47) cf
        (.num (-3))) ∧
    guardAt (iRes (BA real) (.var "read") (.var "u") 49).qualType.pred 0 = true ∧
    guardAt (iRes (BB real) (.var "read") (.var "u") 47).qualType.pred 1 = true :=
  ⟨⟨reachA facts_real chain_real tenvA_real, callA facts_real chain_real⟩,
   ⟨reachB facts_real chain_real tenvB_real, callB facts_real chain_real⟩,
   chain_real.2.2.2.2.1, chain_real.2.2.2.2.2.2.2.2.2⟩

/-- **The premise reads tag 0**: with every tag false it fails at the first
    call, which returns 1. -/
theorem prog_tag0 :
    typecheck (C0 allF) prog 60 = .ok (rootRes allF) ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ (rootRes allF).tagLog') β →
      ¬ ExternCallsMatch predSat (S0 allF)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ (rootRes allF).tagLog') β) := by
  have hf := facts_allF
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht9, _, hd0, _, hall⟩ := hf
  refine ⟨eq_okVal hp, ?_, fun _ => predSatLaws_geSat (geTable_of_allGe hall)⟩
  intro predSat _ hlaws
  obtain ⟨entry, cf, hcall⟩ := callA facts_allF chain_allF
  exact refute_gen hlaws hd0 (reachA facts_allF chain_allF tenvA_allF)
    hcall ht9 chain_allF.2.2.2.2.1
    regime_allF (by decide)

/-! ### The guards the run tests -/

/-- The run reaches no conditional, so the condition on the guards it tests
    holds for every view. -/
private theorem tests_of {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (β : BindVals) : TestsAgreeWithView β (S0 pol) := by
  refine ⟨?_⟩
  intro ctx e1 e2 e3 f cfg _ _ _ _ hreach _ _ _
  have hs := inSet_reach hf hreach
  generalize hst : (⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ : Step) = st at hs
  exfalso
  cases hs with
  | leaf hl => subst hst; exact noAppIte_ne_ite hl rfl
  | _ => simp [S0, S2, S4, S5, S6, S9, S10, S13, prog, B1, B2, B3, A1, A2, bodyF] at hst

/-- `TestsAgreeWithView` for the run under the vector it follows, for every view. -/
theorem tests_real (β : BindVals) : TestsAgreeWithView β (S0 real) := tests_of facts_real β

end Wrapper

/-! ## A call in the taken branch and a call in the skipped branch

`let read = … in let a = read 1 in if a >= 0 then read (0 - 3) else read 4`

The typing allocates tag 0 for `read 1`, tag 1 for the call in the then-branch
and tag 2 for the call in the else-branch. The run returns 1, takes the
then-branch and returns -3 there; it never makes the call of tag 2. So *match*
holds for tag 0 true and tag 1 false, whatever tag 2 is, and fails when all
tags are true. -/

namespace Skipped

open Wrapper (cfg0 cfg1 readV C0 C1 r0)

def R1 : Expr := .app (.var "read") (.num 1)
def R2 : Expr := .app (.var "read") neg3
def R3 : Expr := .app (.var "read") (.num 4)
def IT : Expr := .ite (ge0 "a") R2 R3
def Q1 : Expr := .vlet "a" R1 IT
def prog : Expr := .vlet "read" (readD false) Q1

/-! ### The run -/

def cfgA : Config := { cfg1 with varEnv := VarEnv.update cfg1.varEnv "a" (.num 1) }

private theorem run_R1 : terminatesTo R1 cfg1 cfg1 (.num 1) :=
  ⟨5, false, by
    simp [beval, R1, cfg1, cfg0, readV, readClo, readD, readRet, VarEnv.lookup, VarEnv.update,
      reg_get', validateExternReturn, valueMatchesTyp, idImpl, List.lookup]⟩

private theorem run_cond : terminatesTo (ge0 "a") cfgA cfgA (.bool true) :=
  ⟨3, false, by simp [beval, ge0, evalOp, cfgA, VarEnv.lookup, VarEnv.update, List.lookup]⟩

private theorem runRead1 :
    ∀ c, c.varEnv = cfg1.varEnv → terminatesTo (.var "read") c c (readClo false cfg0.varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; rfl)

private theorem runReadA :
    ∀ c, c.varEnv = cfgA.varEnv → terminatesTo (.var "read") c c (readClo false cfg0.varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; rfl)

/-! ### Typing, for a policy `pol` -/

def rR1 (pol : ExternId → Tag → Option Bool) : TypeResult := okVal (typecheckExpr (C1 pol) R1 56)
def D2 (pol : ExternId → Tag → Option Bool) : TypeContext :=
  { ctxAfter (C1 pol) (rR1 pol) with
    varEnv := (C1 pol).varEnv.update "a" (rR1 pol).qualType,
    bindEnv := (C1 pol).bindEnv.insert "a" (rR1 pol).nextBind',
    nextBind := (rR1 pol).nextBind' + 1 }

private def mgOk (pol : ExternId → Tag → Option Bool) : Bool :=
  match matchGuard (ge0 "a") (D2 pol).memEnv (D2 pol).varEnv (D2 pol).bindEnv 54 with
  | .ok (k, _) => k == 0
  | .error _ => false

def mgDeps (pol : ExternId → Tag → Option Bool) : Deps :=
  match matchGuard (ge0 "a") (D2 pol).memEnv (D2 pol).varEnv (D2 pol).bindEnv 54 with
  | .ok (_, d) => d
  | .error _ => ∅

private theorem mg_eq {pol : ExternId → Tag → Option Bool} (h : mgOk pol = true) :
    matchGuard (ge0 "a") (D2 pol).memEnv (D2 pol).varEnv (D2 pol).bindEnv 54 =
      .ok (0, mgDeps pol) := by
  unfold mgOk at h
  unfold mgDeps
  split at h
  · rename_i k d hk
    simp only [beq_iff_eq] at h
    subst h
    rw [hk]
  · cases h

/-- The condition typed in pure mode, and the then-branch context. -/
def rC (pol : ExternId → Tag → Option Bool) : TypeResult :=
  okVal (typecheckExpr { D2 pol with pureCtx := true } (ge0 "a") 54)
def DT (pol : ExternId → Tag → Option Bool) : TypeContext :=
  ctxTrue (D2 pol) 0 (mgDeps pol) (rC pol)

def rootRes (pol : ExternId → Tag → Option Bool) : TypeResult :=
  okVal (typecheckExpr (C0 pol) prog 60)

def T0 (pol : ExternId → Tag → Option Bool) : Step := ⟨C0 pol, prog, 60, cfg0⟩
private def T1 (pol : ExternId → Tag → Option Bool) : Step := ⟨C1 pol, Q1, 58, cfg1⟩
def T2 (pol : ExternId → Tag → Option Bool) : Step := ⟨C1 pol, R1, 56, cfg1⟩
private def T3 (pol : ExternId → Tag → Option Bool) : Step := ⟨D2 pol, IT, 56, cfgA⟩
def T4 (pol : ExternId → Tag → Option Bool) : Step := ⟨DT pol, R2, 54, cfgA⟩

/-- Tag 0 true, tag 1 false; tag 2 false. -/
def realF : ExternId → Tag → Option Bool := on7 (· == 0)

/-- Tag 0 true, tag 1 false; tag 2 true. -/
def realT : ExternId → Tag → Option Bool := on7 (· != 1)

/-- Every tag true. -/
def bad : ExternId → Tag → Option Bool := on7 fun _ => true

/-- Every tag false. -/
def allF : ExternId → Tag → Option Bool := on7 fun _ => false

section Facts
variable (pol : ExternId → Tag → Option Bool)

private def facts : Bool :=
  isOkB (typecheckExpr (C0 pol) prog 60) &&
  isOkB (typecheckExpr (C0 pol) (readD false) 58) &&
  isOkB (typecheckExpr (C1 pol) R1 56) &&
  isOkB (typecheckExpr (C1 pol) (.num 1) 54) &&
  isOkB (typecheckExpr (ctxAfter (C1 pol) (iArg (C1 pol) (.num 1) 54)) (.var "read") 54) &&
  isParrow1 (iFun (C1 pol) (.var "read") (.num 1) 54).qualType.etyp &&
  mgOk pol &&
  ((D2 pol).regime.lookup? 0 == some true) &&
  isOkB (typecheckExpr { D2 pol with pureCtx := true } (ge0 "a") 54) &&
  isOkB (typecheckExpr (DT pol) neg3 52) &&
  isOkB (typecheckExpr (ctxAfter (DT pol) (iArg (DT pol) neg3 52)) (.var "read") 52) &&
  isParrow1 (iFun (DT pol) (.var "read") neg3 52).qualType.etyp &&
  ((iRes (C1 pol) (.var "read") (.num 1) 54).tagLog'.map (·.tag) == [0]) &&
  ((iRes (DT pol) (.var "read") neg3 52).tagLog'.map (·.tag) == [1]) &&
  descGe (programTable ∅ (rootRes pol).tagLog') 0 &&
  descGe (programTable ∅ (rootRes pol).tagLog') 1 &&
  allGe (rootRes pol).tagLog'

end Facts

private theorem facts_realF : facts realF = true := by decide +kernel
private theorem facts_realT : facts realT = true := by decide +kernel
private theorem facts_bad : facts bad = true := by decide +kernel

/-- The regime entries the two calls leave, and the tags the program table
    holds. -/
private theorem regimes :
    (iRes (C1 realF) (.var "read") (.num 1) 54).regime'.lookup? 0 = some true ∧
    (iRes (DT realF) (.var "read") neg3 52).regime'.lookup? 1 = some false ∧
    (iRes (C1 realT) (.var "read") (.num 1) 54).regime'.lookup? 0 = some true ∧
    (iRes (DT realT) (.var "read") neg3 52).regime'.lookup? 1 = some false ∧
    (iRes (DT bad) (.var "read") neg3 52).regime'.lookup? 1 = some true ∧
    (rootRes realF).tagLog'.map (·.tag) = [0, 1, 2] := by
  decide +kernel

/-! ### The steps the run reaches -/

private inductive InSet (pol : ExternId → Tag → Option Bool) : Step → Prop
  | t0 : InSet pol (T0 pol)
  | t1 : InSet pol (T1 pol)
  | t2 : InSet pol (T2 pol)
  | t3 : InSet pol (T3 pol)
  | t4 : InSet pol (T4 pol)
  | leaf {s : Step} : noAppIte s.e = true → InSet pol s

private theorem inSet_step {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    {s s' : Step} (hs : InSet pol s) (h : SubStep s s') : InSet pol s' := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, h0, hR1, _, _, _, hmg, hreg0, hrC, _⟩ := hf
  cases hs with
  | t0 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := C0 pol) (x := "read") (e1 := readD false)
        (e2 := Q1) (F := 60) (cfg := cfg0) h
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl : r1 = r0 pol := ok_inj h1 (eq_okVal h0)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 (run_readD false cfg0 rfl)
        exact InSet.t1
  | t1 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := C1 pol) (x := "a") (e1 := R1)
        (e2 := IT) (F := 58) (cfg := cfg1) h
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.t2
      · obtain rfl : r1 = rR1 pol := ok_inj h1 (eq_okVal hR1)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 run_R1
        exact InSet.t3
  | t3 =>
      obtain ⟨f, hf, h⟩ := SubStep.ite_inv (ctx := D2 pol) (e1 := ge0 "a") (e2 := R2) (e3 := R3)
        (F := 56) (cfg := cfgA) h
      obtain rfl : f = 54 := by omega
      have hmg' := mg_eq hmg
      have hstd : ¬ StdArm (D2 pol) (ge0 "a") 54 := by
        rintro (⟨msg, hmsg⟩ | ⟨k, deps, hk, hnone⟩)
        · rw [hmg'] at hmsg; cases hmsg
        · rw [hmg'] at hk
          cases hk
          rw [hreg0] at hnone
          cases hnone
      rcases h with ⟨k, deps, b, _, _, rfl⟩ |
          ⟨k, deps, b, r1, c1, hk, _, h1, hr1, rfl⟩ |
          ⟨k, deps, b, r1, r2, c1, _, _, _, hr1, _⟩ |
          ⟨hs, _⟩ | ⟨_, _, hs, _⟩ | ⟨_, _, _, hs, _⟩
      · exact InSet.leaf rfl
      · rw [hmg'] at hk
        cases hk
        obtain rfl : r1 = rC pol := ok_inj h1 (eq_okVal hrC)
        obtain ⟨rfl, _⟩ := terminatesTo_det hr1 run_cond
        exact InSet.t4
      · have := terminatesTo_det hr1 run_cond
        simp at this
      · exact absurd hs hstd
      · exact absurd hs hstd
      · exact absurd hs hstd
  | t2 =>
      exact InSet.leaf (readCall_sub (B := C1 pol) (fe := .var "read") (arg := .num 1)
        (F := 56) (cfgB := cfg1) rfl rfl runRead1 (run_num _ _) h)
  | t4 =>
      exact InSet.leaf (readCall_sub (B := DT pol) (fe := .var "read") (arg := neg3)
        (F := 54) (cfgB := cfgA) rfl rfl runReadA (run_neg3 _) h)
  | leaf hl => exact InSet.leaf (SubStep.noAppIte h hl)

private theorem inSet_reach {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    {s : Step} (h : Reach (T0 pol) s) : InSet pol s := by
  induction h with
  | refl => exact InSet.t0
  | tail _ hsub ih => exact inSet_step hf ih hsub

/-- The two calls the run makes; the call in the else-branch is not among
    them. -/
private theorem inSet_call {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    {s : Step} {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {o : Value}
    (hs : InSet pol s) (h : ExternCallAt s effects entry res cf o) :
    (res = iRes (C1 pol) (.var "read") (.num 1) 54 ∧ o = .num 1 ∧ effects = []) ∨
    (res = iRes (DT pol) (.var "read") neg3 52 ∧ o = .num (-3) ∧ effects = []) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, hu2, hr2, hp2, _, _, _, hu4, hr4, hp4, _⟩ := hf
  cases hs with
  | t0 => cases h
  | t1 => cases h
  | t3 => cases h
  | t2 =>
      obtain ⟨rfl, rfl, _, rfl, _⟩ := readCall_call (B := C1 pol) (fe := .var "read")
        (arg := .num 1) (G := 54) (cfgB := cfg1) runRead1 (run_num _ _) rfl hu2 hr2 hp2 h
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | t4 =>
      obtain ⟨rfl, rfl, _, rfl, _⟩ := readCall_call (B := DT pol) (fe := .var "read")
        (arg := neg3) (G := 52) (cfgB := cfgA) runReadA (run_neg3 _) rfl hu4 hr4 hp4 h
      exact Or.inr ⟨rfl, rfl, rfl⟩
  | leaf hl =>
      exact absurd h (ExternCallAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _))

/-- No step of the set declares an `extern val`. -/
private theorem inSet_val {pol : ExternId → Tag → Option Bool} {s : Step} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet pol s) :
    ¬ ExternValAt s res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternValAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _) h
  | _ => cases h

private theorem match_of {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (h0 : (iRes (C1 pol) (.var "read") (.num 1) 54).regime'.lookup? 0 = some true)
    (h1 : (iRes (DT pol) (.var "read") neg3 52).regime'.lookup? 1 = some false)
    (predSat : PredSat) {β : BindVals}
      (hlaws : PredSatLaws predSat (programTable ∅ (rootRes pol).tagLog') β) :
    ExternCallsMatch predSat (T0 pol) := by
  have hf' := hf
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf'
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ht2, ht4, hd0, hd1, _⟩ := hf'
  refine ⟨fun s effects entry res cf o hreach hcall => ?_,
    fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hf hreach))⟩
  rcases inSet_call hf (inSet_reach hf hreach) hcall with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact callMatches_of hlaws hd0 ht2 h0 (by decide)
  · exact callMatches_of hlaws hd1 ht4 h1 (by decide)

/-- **The premise holds for tag 0 true and tag 1 false, whichever value the
    skipped tag 2 has**, for every `predSat` lawful on the program table; and
    such a `predSat` exists. -/
theorem prog_real :
    (rootRes realF).tagLog'.map (·.tag) = [0, 1, 2] ∧
    typecheck (C0 realF) prog 60 = .ok (rootRes realF) ∧
    typecheck (C0 realT) prog 60 = .ok (rootRes realT) ∧
    realF 7 2 = some false ∧ realT 7 2 = some true ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ (rootRes realF).tagLog') β →
      ExternCallsMatch predSat (T0 realF)) ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ (rootRes realT).tagLog') β →
      ExternCallsMatch predSat (T0 realT)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ (rootRes realF).tagLog') β) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ (rootRes realT).tagLog') β) := by
  obtain ⟨hF0, hF1, hT0, hT1, _, htags⟩ := regimes
  have hF := facts_realF
  have hT := facts_realT
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hF hT
  refine ⟨htags, eq_okVal hF.1, eq_okVal hT.1, rfl, rfl,
    match_of facts_realF hF0 hF1, match_of facts_realT hT0 hT1,
    fun _ => predSatLaws_geSat (geTable_of_allGe hF.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2),
    fun _ => predSatLaws_geSat (geTable_of_allGe hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)⟩

/-- *Agreement* holds for two copies of the run under the vector `realF`: its
    two calls have different member results. -/
theorem agree_self : ExternCallsAgree (T0 realF) (T0 realF) := by
  have hf := facts_realF
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ht2, ht4, _⟩ := hf
  have hne := ne_of_tags ht2 ht4 (by decide)
  refine agree_self_of fun s₀ s₁ _ _ _ res _ _ o₀ o₁ hr₀ hr₁ hc₀ hc₁ => ?_
  rcases inSet_call facts_realF (inSet_reach facts_realF hr₀) hc₀ with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    rcases inSet_call facts_realF (inSet_reach facts_realF hr₁) hc₁ with
      ⟨h, rfl, -⟩ | ⟨h, rfl, -⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd h hne
  · exact absurd h.symm hne
  · exact ⟨rfl, rfl⟩

/-! ### The skipped call

The else-branch is typed against the regime before the `if`, and the `if`
keeps the regime of the taken branch, so the entry for tag 2 lives only in the
result of the skipped call. That call allocates tag 2 and records the policy
value there (false for `realF`, true for `realT`); the run never reaches it,
so *match* does not constrain tag 2. -/

def rR2 (pol : ExternId → Tag → Option Bool) : TypeResult := okVal (typecheckExpr (DT pol) R2 54)
def DF (pol : ExternId → Tag → Option Bool) : TypeContext :=
  ctxFalse' (D2 pol) 0 (mgDeps pol) (rR2 pol)

theorem skipped_call :
    isOkB (typecheckExpr (DF realF) R3 54) = true ∧
    (okVal (typecheckExpr (DF realF) R3 54)).tagLog'.map (·.tag) = [2] ∧
    (iRes (DF realF) (.var "read") (.num 4) 52).tagLog'.map (·.tag) = [2] ∧
    (iRes (DF realF) (.var "read") (.num 4) 52).regime'.lookup? 2 = some false ∧
    isOkB (typecheckExpr (DF realT) R3 54) = true ∧
    (iRes (DF realT) (.var "read") (.num 4) 52).tagLog'.map (·.tag) = [2] ∧
    (iRes (DF realT) (.var "read") (.num 4) 52).regime'.lookup? 2 = some true ∧
    (rootRes realF).regime'.lookup? 2 = none := by
  decide +kernel

/-! ### The vector true, true -/

private theorem facts_bad_chain :
    let E' := (iFun (DT bad) (.var "read") neg3 52).qualType.etyp
    parrowM E' = .extern 7 "b" readRet (extParts (parrowM E')).1 (extParts (parrowM E')).2.1
      (extParts (parrowM E')).2.2 ∧
    isOkB (pfnApply (DT bad) (iArg (DT bad) neg3 52) (iFun (DT bad) (.var "read") neg3 52)
      (parrowS1 E') (parrowS2 E') (parrowP E') 52 (parrowM E')
      (iCursor (DT bad) (.var "read") neg3 52) (iBind (DT bad) (.var "read") neg3 52)) = true ∧
    guardAt (iRes (DT bad) (.var "read") neg3 52).qualType.pred 1 = true := by
  decide +kernel

/-- **The premise fails for the vector true, true**: the call in the taken
    branch returns -3 under a true tag. -/
theorem prog_bad :
    typecheck (C0 bad) prog 60 = .ok (rootRes bad) ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ (rootRes bad).tagLog') β →
      ¬ ExternCallsMatch predSat (T0 bad)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ (rootRes bad).tagLog') β) := by
  have hf := facts_bad
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, h0, hR1, _, _, _, hmg, hreg0, hrC, hu4, hr4, hp4, _, ht4, _, hd1, hall⟩ := hf
  refine ⟨eq_okVal hp, ?_, fun _ => predSatLaws_geSat (geTable_of_allGe hall)⟩
  intro predSat _ hlaws
  obtain ⟨hm, hap, hg⟩ := facts_bad_chain
  have e1 : SubStep (T0 bad) (T1 bad) :=
    SubStep.vletBody (c1 := cfg0) (v1 := readV) (eq_okVal h0) (run_readD false cfg0 rfl)
  have e2 : SubStep (T1 bad) (T3 bad) :=
    SubStep.vletBody (c1 := cfg1) (v1 := .num 1) (eq_okVal hR1) run_R1
  have e3 : SubStep (T3 bad) (T4 bad) :=
    SubStep.iteThenMatched (c1 := cfgA) (mg_eq hmg) hreg0 (eq_okVal hrC) run_cond
  have hreach : Reach (T0 bad) (T4 bad) := .tail (.tail (.tail .refl e1) e2) e3
  obtain ⟨entry, -, hcall⟩ := readCall_mk (B := DT bad) (fe := .var "read") (arg := neg3)
    (G := 52) (cfgB := cfgA) runReadA (run_neg3 _) rfl hu4 hr4 hp4 hm hap
  exact refute_of hlaws hd1 hreach hcall ht4 hg regimes.2.2.2.2.1 (by decide)

/-! ### Both calls the run makes are reached, and the first tag is read

Under tag 0 true and tag 1 false, each of the two calls the run makes is
reached and returns the value the run computes, and its result carries a guard
closure at the call's tag, so *match* does constrain it. The premise also
reads tag 0: with every tag false it fails at the first call, which returns
1. -/

/-- The member result and guard of the first call. -/
private def ChainA (pol : ExternId → Tag → Option Bool) : Prop :=
  let E := (iFun (C1 pol) (.var "read") (.num 1) 54).qualType.etyp
  parrowM E = .extern 7 "b" readRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
    (extParts (parrowM E)).2.2 ∧
  isOkB (pfnApply (C1 pol) (iArg (C1 pol) (.num 1) 54) (iFun (C1 pol) (.var "read") (.num 1) 54)
    (parrowS1 E) (parrowS2 E) (parrowP E) 54 (parrowM E)
    (iCursor (C1 pol) (.var "read") (.num 1) 54)
      (iBind (C1 pol) (.var "read") (.num 1) 54)) = true ∧
  guardAt (iRes (C1 pol) (.var "read") (.num 1) 54).qualType.pred 0 = true

/-- The member result and guard of the call in the taken branch. -/
private def ChainB (pol : ExternId → Tag → Option Bool) : Prop :=
  let E := (iFun (DT pol) (.var "read") neg3 52).qualType.etyp
  parrowM E = .extern 7 "b" readRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
    (extParts (parrowM E)).2.2 ∧
  isOkB (pfnApply (DT pol) (iArg (DT pol) neg3 52) (iFun (DT pol) (.var "read") neg3 52)
    (parrowS1 E) (parrowS2 E) (parrowP E) 52 (parrowM E)
    (iCursor (DT pol) (.var "read") neg3 52) (iBind (DT pol) (.var "read") neg3 52)) = true ∧
  guardAt (iRes (DT pol) (.var "read") neg3 52).qualType.pred 1 = true

/-- What the first call needs from the typing; holds whatever the regime of
    the `if` guard is. -/
private def factsA (pol : ExternId → Tag → Option Bool) : Bool :=
  isOkB (typecheckExpr (C0 pol) prog 60) &&
  isOkB (typecheckExpr (C0 pol) (readD false) 58) &&
  isOkB (typecheckExpr (C1 pol) (.num 1) 54) &&
  isOkB (typecheckExpr (ctxAfter (C1 pol) (iArg (C1 pol) (.num 1) 54)) (.var "read") 54) &&
  isParrow1 (iFun (C1 pol) (.var "read") (.num 1) 54).qualType.etyp &&
  ((iRes (C1 pol) (.var "read") (.num 1) 54).tagLog'.map (·.tag) == [0]) &&
  descGe (programTable ∅ (rootRes pol).tagLog') 0 &&
  allGe (rootRes pol).tagLog'

private theorem chainA_realF : ChainA realF := by unfold ChainA; decide +kernel
private theorem chainB_realF : ChainB realF := by unfold ChainB; decide +kernel
private theorem chainA_allF : ChainA allF := by unfold ChainA; decide +kernel
private theorem factsA_realF : factsA realF = true := by decide +kernel
private theorem factsA_allF : factsA allF = true := by decide +kernel
private theorem regime_allF :
    (iRes (C1 allF) (.var "read") (.num 1) 54).regime'.lookup? 0 = some false := by
  decide +kernel

private theorem reachA {pol : ExternId → Tag → Option Bool} (hf : factsA pol = true) :
    Reach (T0 pol) (T2 pol) := by
  simp only [factsA, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, h0, _⟩ := hf
  have e1 : SubStep (T0 pol) (T1 pol) :=
    SubStep.vletBody (c1 := cfg0) (v1 := readV) (eq_okVal h0) (run_readD false cfg0 rfl)
  have e2 : SubStep (T1 pol) (T2 pol) := SubStep.vletBound
  exact .tail (.tail .refl e1) e2

private theorem callA {pol : ExternId → Tag → Option Bool} (hf : factsA pol = true)
    (hc : ChainA pol) :
    ∃ entry cf,
      ExternCallAt (T2 pol) [] entry (iRes (C1 pol) (.var "read") (.num 1) 54) cf (.num 1) := by
  simp only [factsA, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, hu2, hr2, hp2, _⟩ := hf
  obtain ⟨hm, hap, _⟩ := hc
  obtain ⟨entry, -, h⟩ := readCall_mk (B := C1 pol) (fe := .var "read") (arg := .num 1)
    (G := 54) (cfgB := cfg1) runRead1 (run_num _ _) rfl hu2 hr2 hp2 hm hap
  exact ⟨entry, _, h⟩

private theorem reachB {pol : ExternId → Tag → Option Bool} (hf : facts pol = true) :
    Reach (T0 pol) (T4 pol) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, h0, hR1, _, _, _, hmg, hreg0, hrC, _⟩ := hf
  have e1 : SubStep (T0 pol) (T1 pol) :=
    SubStep.vletBody (c1 := cfg0) (v1 := readV) (eq_okVal h0) (run_readD false cfg0 rfl)
  have e2 : SubStep (T1 pol) (T3 pol) :=
    SubStep.vletBody (c1 := cfg1) (v1 := .num 1) (eq_okVal hR1) run_R1
  have e3 : SubStep (T3 pol) (T4 pol) :=
    SubStep.iteThenMatched (c1 := cfgA) (mg_eq hmg) hreg0 (eq_okVal hrC) run_cond
  exact .tail (.tail (.tail .refl e1) e2) e3

private theorem callB {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (hc : ChainB pol) :
    ∃ entry cf,
      ExternCallAt (T4 pol) [] entry (iRes (DT pol) (.var "read") neg3 52) cf (.num (-3)) := by
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, _, _, _, _, hu4, hr4, hp4, _⟩ := hf
  obtain ⟨hm, hap, _⟩ := hc
  obtain ⟨entry, -, h⟩ := readCall_mk (B := DT pol) (fe := .var "read") (arg := neg3) (G := 52)
    (cfgB := cfgA) runReadA (run_neg3 _) rfl hu4 hr4 hp4 hm hap
  exact ⟨entry, _, h⟩

/-- **Under tag 0 true and tag 1 false both calls the run makes are reached**,
    return 1 and -3, and carry guard closures at tags 0 and 1: `prog_real`
    constrains both. -/
theorem prog_live :
    (Reach (T0 realF) (T2 realF) ∧ ∃ entry cf,
      ExternCallAt (T2 realF) [] entry (iRes (C1 realF) (.var "read") (.num 1) 54) cf
        (.num 1)) ∧
    (Reach (T0 realF) (T4 realF) ∧ ∃ entry cf,
      ExternCallAt (T4 realF) [] entry (iRes (DT realF) (.var "read") neg3 52) cf
        (.num (-3))) ∧
    guardAt (iRes (C1 realF) (.var "read") (.num 1) 54).qualType.pred 0 = true ∧
    guardAt (iRes (DT realF) (.var "read") neg3 52).qualType.pred 1 = true :=
  ⟨⟨reachA factsA_realF, callA factsA_realF chainA_realF⟩,
   ⟨reachB facts_realF, callB facts_realF chainB_realF⟩,
   chainA_realF.2.2, chainB_realF.2.2⟩

/-- **The premise reads tag 0**: with every tag false it fails at the first
    call, which returns 1. -/
theorem prog_tag0 :
    typecheck (C0 allF) prog 60 = .ok (rootRes allF) ∧
    (∀ (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ (rootRes allF).tagLog') β →
      ¬ ExternCallsMatch predSat (T0 allF)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ (rootRes allF).tagLog') β) := by
  have hf := factsA_allF
  simp only [factsA, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, _, _, _, _, ht, hd0, hall⟩ := hf
  refine ⟨eq_okVal hp, ?_, fun _ => predSatLaws_geSat (geTable_of_allGe hall)⟩
  intro predSat _ hlaws
  obtain ⟨entry, cf, hcall⟩ := callA factsA_allF chainA_allF
  exact refute_gen hlaws hd0 (reachA factsA_allF) hcall ht chainA_allF.2.2 regime_allF
    (by decide)

/-! ### The guards the run tests -/

/-- The one conditional the run reaches is `IT`, in the context `D2`. -/
private theorem tests_of {pol : ExternId → Tag → Option Bool} (hf : facts pol = true)
    (harg : envArgOnly (D2 pol).varEnv (D2 pol).memEnv = true) (β : BindVals) :
    TestsAgreeWithView β (T0 pol) := by
  refine ⟨?_⟩
  intro ctx e1 e2 e3 f cfg _ _ _ _ hreach _ _ hd
  have hs := inSet_reach hf hreach
  generalize hst : (⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ : Step) = st at hs
  cases hs with
  | t3 =>
      simp only [T3, Step.mk.injEq] at hst
      obtain ⟨rfl, -, -, -⟩ := hst
      exact viewAgrees_of_envArgOnly harg β _ hd
  | leaf hl => subst hst; exact absurd rfl (noAppIte_ne_ite hl)
  | _ => simp [T0, T1, T2, T4, prog, Q1, R1, R2] at hst

/-- Every guard of the context of the conditional reads only its argument. -/
private theorem argOnly_realF : envArgOnly (D2 realF).varEnv (D2 realF).memEnv = true := by
  decide +kernel

/-- `TestsAgreeWithView` for the run under `realF`, for every view: the guards
    at the conditional read only their argument. -/
theorem tests_realF (β : BindVals) : TestsAgreeWithView β (T0 realF) :=
  tests_of facts_realF argOnly_realF β

end Skipped

/-! ## One call, two runs

`let read = … in read x`, with `x` a poisoned input of type `int`

The declaration accepts a poisoned argument. The call allocates tag 0; the
regime sets it true. The program's result is the call's result, guarded by
tag 0. Two runs start with `x = n₀` and `x = n₁`; the start states agree on
the clean part, since `x` is poisoned. Both outputs pass the check when
`n₀, n₁ ≥ 0`, so *match* holds in each run, but *agreement* holds exactly when
`n₀ = n₁`. -/

namespace TwoRuns

def allT : ExternId → Tag → Option Bool := on7 fun _ => true

def call : Expr := .app (.var "read") (.var "x")
def prog : Expr := .vlet "read" (readD true) call

def K0 : TypeContext :=
  { ctxWith allT with varEnv := (∅ : VarTypeEnv).update "x" pInt }
private def rD : TypeResult := okVal (typecheckExpr K0 (readD true) 58)
private def K1 : TypeContext :=
  { ctxAfter K0 rD with
    varEnv := K0.varEnv.update "read" rD.qualType,
    bindEnv := K0.bindEnv.insert "read" rD.nextBind',
    nextBind := rD.nextBind' + 1 }
def rootRes : TypeResult := okVal (typecheckExpr K0 prog 60)
private def callRes : TypeResult := iRes K1 (.var "read") (.var "x") 56

/-- The start state with `x = n`, and the state after the declaration. -/
def cfgX (n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update [] "x" (.num n), nextAddr := 0, pureMode := false,
    registry := reg }
private def cfgX1 (n : Int) : Config :=
  { cfgX n with varEnv := (cfgX n).varEnv.update "read" (readClo true (cfgX n).varEnv) }

def U0 (n : Int) : Step := ⟨K0, prog, 60, cfgX n⟩
private def U1 (n : Int) : Step := ⟨K1, call, 58, cfgX1 n⟩

private theorem runRead (n : Int) :
    ∀ c, c.varEnv = (cfgX1 n).varEnv →
      terminatesTo (.var "read") c c (readClo true (cfgX n).varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; rfl)

private theorem runX (n : Int) : terminatesTo (.var "x") (cfgX1 n) (cfgX1 n) (.num n) :=
  run_var rfl

private def facts : Bool :=
  isOkB (typecheckExpr K0 prog 60) &&
  isOkB (typecheckExpr K0 (readD true) 58) &&
  isOkB (typecheckExpr K1 (.var "x") 56) &&
  isOkB (typecheckExpr (ctxAfter K1 (iArg K1 (.var "x") 56)) (.var "read") 56) &&
  isParrow1 (iFun K1 (.var "read") (.var "x") 56).qualType.etyp &&
  (callRes.tagLog'.map (·.tag) == [0]) &&
  (callRes.regime'.lookup? 0 == some true) &&
  (qtypGuardTag callRes.qualType == some 0) &&
  (callRes.qualType.etyp == ETyp.int) &&
  descGe (programTable ∅ rootRes.tagLog') 0 &&
  allGe rootRes.tagLog' &&
  (qtypGuardTag rootRes.qualType == some 0) &&
  (rootRes.regime'.lookup? 0 == some true) &&
  (rootRes.qualType.etyp == ETyp.int)

private theorem facts_ok : facts = true := by decide +kernel

private theorem call_chain :
    let E := (iFun K1 (.var "read") (.var "x") 56).qualType.etyp
    parrowM E = .extern 7 "b" readRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
      (extParts (parrowM E)).2.2 ∧
    isOkB (pfnApply K1 (iArg K1 (.var "x") 56) (iFun K1 (.var "read") (.var "x") 56)
      (parrowS1 E) (parrowS2 E) (parrowP E) 56 (parrowM E)
      (iCursor K1 (.var "read") (.var "x") 56) (iBind K1 (.var "read") (.var "x") 56)) = true := by
  decide +kernel

/-! ### The steps a run reaches -/

private inductive InSet (n : Int) : Step → Prop
  | u0 : InSet n (U0 n)
  | u1 : InSet n (U1 n)
  | leaf {s : Step} : noAppIte s.e = true → InSet n s

private theorem inSet_step {n : Int} {s s' : Step} (hs : InSet n s) (h : SubStep s s') :
    InSet n s' := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hD, _⟩ := hf
  cases hs with
  | u0 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := K0) (x := "read") (e1 := readD true)
        (e2 := call) (F := 60) (cfg := cfgX n) h
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl : r1 = rD := ok_inj h1 (eq_okVal hD)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 (run_readD true (cfgX n) rfl)
        exact InSet.u1
  | u1 =>
      exact InSet.leaf (readCall_sub (B := K1) (fe := .var "read") (arg := .var "x")
        (F := 58) (cfgB := cfgX1 n) rfl rfl (runRead n) (runX n) h)
  | leaf hl => exact InSet.leaf (SubStep.noAppIte h hl)

private theorem inSet_reach {n : Int} {s : Step} (h : Reach (U0 n) s) : InSet n s := by
  induction h with
  | refl => exact InSet.u0
  | tail _ hsub ih => exact inSet_step ih hsub

/-- The run makes one call; it returns `n`. -/
private theorem inSet_call {n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet n s) (h : ExternCallAt s effects entry res cf o) :
    res = callRes ∧ o = .num n ∧ effects = [] := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, hu, hr, hp, _⟩ := hf
  cases hs with
  | u0 => cases h
  | u1 =>
      obtain ⟨h1, h2, _, h3, _⟩ := readCall_call (B := K1) (fe := .var "read") (arg := .var "x")
        (G := 56) (cfgB := cfgX1 n) (runRead n) (runX n) rfl hu hr hp h
      exact ⟨h1, h2, h3⟩
  | leaf hl =>
      exact absurd h (ExternCallAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _))

/-- No step of the set declares an `extern val`. -/
private theorem inSet_val {n : Int} {s : Step} {res : TypeResult} {cf : Config} {o : Value} (hs : InSet n s) :
    ¬ ExternValAt s res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternValAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _) h
  | _ => cases h

private theorem reach_call (n : Int) :
    Reach (U0 n) (U1 n) ∧
    ∃ entry, entry.bodyCtx = iBody K1 (.var "read") (.var "x") 56 ∧
      ExternCallAt (U1 n) [] entry callRes (cfgX1 n) (.num n) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hD, hu, hr, hp, _⟩ := hf
  obtain ⟨hm, hap⟩ := call_chain
  refine ⟨.tail .refl ?_, readCall_mk (runRead n) (runX n) rfl hu hr hp hm hap⟩
  exact SubStep.vletBody (c1 := cfgX n) (v1 := readClo true (cfgX n).varEnv) (eq_okVal hD)
    (run_readD true (cfgX n) rfl)

/-! ### The premises -/

/-- *Match* holds in a run whose output passes the check. -/
theorem match_of {n : Int} (hn : 0 ≤ n) (predSat : PredSat)
    {β : BindVals} (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β) :
    ExternCallsMatch predSat (U0 n) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, _, _, ht, hreg, _, _, hd, _⟩ := hf
  refine ⟨fun s effects entry res cf o hreach hcall => ?_,
    fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
  obtain ⟨rfl, rfl, rfl⟩ := inSet_call (inSet_reach hreach) hcall
  exact callMatches_of hlaws hd ht hreg (by simp [hn])

/-- *Agreement* for the pair holds exactly when the two runs start with the
    same `x`. -/
theorem agree_iff (n₀ n₁ : Int) : ExternCallsAgree (U0 n₀) (U0 n₁) ↔ n₀ = n₁ := by
  constructor
  · intro h
    have hf := facts_ok
    simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
    obtain ⟨_, _, _, _, _, ht, hreg, hg, hety, _⟩ := hf
    obtain ⟨hr₀, e₀, hb₀, hc₀⟩ := reach_call n₀
    obtain ⟨hr₁, e₁, hb₁, hc₁⟩ := reach_call n₁
    by_contra hne
    exact callAgrees_false ht hg hreg hety (by simpa using hne)
      (h.calls _ _ _ _ _ _ _ _ _ _ hr₀ hr₁ rfl rfl rfl hc₀ hc₁ (hb₀.trans hb₁.symm))
  · rintro rfl
    refine ⟨fun s₀ s₁ _ _ _ res _ _ o₀ o₁ hr₀ hr₁ _ _ _ hc₀ hc₁ _ => ?_⟩
    obtain ⟨rfl, rfl, rfl⟩ := inSet_call (inSet_reach hr₀) hc₀
    obtain ⟨_, rfl, -⟩ := inSet_call (inSet_reach hr₁) hc₁
    exact callAgrees_nil rfl

/-- **One call, two runs.** The typing accepts the program; its result is the
    call's, guarded by tag 0, which the regime sets true. *Match* holds in the
    runs with `x = 5` and `x = 7` for every lawful `predSat` (and one exists).
    *Agreement* holds for the pair 5, 5 and fails for the pair 5, 7. -/
theorem agree_case :
    typecheck K0 prog 60 = .ok rootRes ∧
    qtypGuardTag rootRes.qualType = some 0 ∧ rootRes.regime'.lookup? 0 = some true ∧
    (∀ (predSat : PredSat) (β : BindVals), PredSatLaws predSat (programTable ∅ rootRes.tagLog') β →
      ExternCallsMatch predSat (U0 5) ∧ ExternCallsMatch predSat (U0 7)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ rootRes.tagLog') β) ∧
    ExternCallsAgree (U0 5) (U0 5) ∧
    ¬ ExternCallsAgree (U0 5) (U0 7) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, _, _, _, _, _, _, _, _, _, hall, hg, hreg, _⟩ := hf
  refine ⟨eq_okVal hp, hg, hreg, fun predSat _ hlaws =>
    ⟨match_of (by decide) predSat hlaws, match_of (by decide) predSat hlaws⟩,
    fun _ => predSatLaws_geSat (geTable_of_allGe hall), (agree_iff 5 5).2 rfl, ?_⟩
  rw [agree_iff]
  decide

/-! ### The guards the run tests -/

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
  | _ => simp [U0, U1, prog, call] at hst

end TwoRuns

/-! ## Two tagged calls in each of two runs

  `let read = … in let a = read x in read y`, with `x` and `y` poisoned inputs
  of type `int`

The declaration accepts a poisoned argument. The first call allocates tag 0,
the second tag 1; the policy sets both true. A run that starts with `x = m`
and `y = n` makes two calls: the first returns `m`, the second `n`.

The two calls of a run are told apart: their steps differ in the expression
(`read x`, `read y`) and in the typing context (the tag counter is 0 at the
first and 1 at the second). So *agreement* pairs the first call of one run
with the first call of the other, and the second with the second. It holds for
the runs (5, 7) and (5, 7); a pairing that crossed the calls would compare 5
with 7 and fail. It fails for the runs (5, 7) and (5, 8), at the second call.
-/

namespace TwoCalls

/-- Every call of `read` gets `true` from the policy; no other extern gets a value. -/
def allT : ExternId → Tag → Option Bool := on7 fun _ => true

def C1 : Expr := .app (.var "read") (.var "x")
def C2 : Expr := .app (.var "read") (.var "y")
def Q : Expr := .vlet "a" C1 C2
def prog : Expr := .vlet "read" (readD true) Q

/-- The typing contexts of the steps: the program, the body of the first `let`,
    and the body of the second. -/
def K0 : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅,
    varEnv := ((∅ : VarTypeEnv).update "x" pInt).update "y" pInt, tagEnv := ∅,
    nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := allT }
def rD : TypeResult := okVal (typecheckExpr K0 (readD true) 58)
def K1 : TypeContext := { ctxAfter K0 rD with
                          varEnv := K0.varEnv.update "read" rD.qualType,
                          bindEnv := K0.bindEnv.insert "read" rD.nextBind',
                          nextBind := rD.nextBind' + 1 }
def rC1 : TypeResult := okVal (typecheckExpr K1 C1 56)
def K2 : TypeContext := { ctxAfter K1 rC1 with
                          varEnv := K1.varEnv.update "a" rC1.qualType,
                          bindEnv := K1.bindEnv.insert "a" rC1.nextBind',
                          nextBind := rC1.nextBind' + 1 }
def rootRes : TypeResult := okVal (typecheckExpr K0 prog 60)

/-- The member results of the two calls. -/
def res1 : TypeResult := iRes K1 (.var "read") (.var "x") 54
def res2 : TypeResult := iRes K2 (.var "read") (.var "y") 54

/-- The start state with `x = m` and `y = n`, and the states of the two `let`
    bodies. -/
def cfg0 (m n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update (VarEnv.update [] "x" (.num m)) "y" (.num n),
    nextAddr := 0, pureMode := false, registry := reg }
def cfg1 (m n : Int) : Config :=
  { cfg0 m n with varEnv := (cfg0 m n).varEnv.update "read" (readClo true (cfg0 m n).varEnv) }
def cfg2 (m n : Int) : Config :=
  { cfg1 m n with varEnv := (cfg1 m n).varEnv.update "a" (.num m) }

def V0 (m n : Int) : Step := ⟨K0, prog, 60, cfg0 m n⟩
def V1 (m n : Int) : Step := ⟨K1, Q, 58, cfg1 m n⟩
def V2 (m n : Int) : Step := ⟨K1, C1, 56, cfg1 m n⟩
def V3 (m n : Int) : Step := ⟨K2, C2, 56, cfg2 m n⟩

private def facts : Bool :=
  isOkB (typecheckExpr K0 prog 60) &&
  isOkB (typecheckExpr K0 (readD true) 58) &&
  isOkB (typecheckExpr K1 C1 56) &&
  isOkB (typecheckExpr K1 (.var "x") 54) &&
  isOkB (typecheckExpr (ctxAfter K1 (iArg K1 (.var "x") 54)) (.var "read") 54) &&
  isParrow1 (iFun K1 (.var "read") (.var "x") 54).qualType.etyp &&
  isOkB (typecheckExpr K2 (.var "y") 54) &&
  isOkB (typecheckExpr (ctxAfter K2 (iArg K2 (.var "y") 54)) (.var "read") 54) &&
  isParrow1 (iFun K2 (.var "read") (.var "y") 54).qualType.etyp &&
  (res1.tagLog'.map (·.tag) == [0]) &&
  (res2.tagLog'.map (·.tag) == [1]) &&
  (res1.regime'.lookup? 0 == some true) &&
  (res2.regime'.lookup? 1 == some true) &&
  (qtypGuardTag res1.qualType == some 0) &&
  (qtypGuardTag res2.qualType == some 1) &&
  (res1.qualType.etyp == ETyp.int) &&
  (res2.qualType.etyp == ETyp.int) &&
  descGe (programTable ∅ rootRes.tagLog') 0 &&
  descGe (programTable ∅ rootRes.tagLog') 1 &&
  allGe rootRes.tagLog' &&
  (K1.nextTag == 0) &&
  (K2.nextTag == 1)

private theorem facts_ok : facts = true := by decide +kernel

private theorem calls_chain :
    (let E := (iFun K1 (.var "read") (.var "x") 54).qualType.etyp
     parrowM E = .extern 7 "b" readRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
       (extParts (parrowM E)).2.2 ∧
     isOkB (pfnApply K1 (iArg K1 (.var "x") 54) (iFun K1 (.var "read") (.var "x") 54)
       (parrowS1 E) (parrowS2 E) (parrowP E) 54 (parrowM E)
       (iCursor K1 (.var "read") (.var "x") 54) (iBind K1 (.var "read") (.var "x") 54)) = true) ∧
    (let E := (iFun K2 (.var "read") (.var "y") 54).qualType.etyp
     parrowM E = .extern 7 "b" readRet (extParts (parrowM E)).1 (extParts (parrowM E)).2.1
       (extParts (parrowM E)).2.2 ∧
     isOkB (pfnApply K2 (iArg K2 (.var "y") 54) (iFun K2 (.var "read") (.var "y") 54)
       (parrowS1 E) (parrowS2 E) (parrowP E) 54 (parrowM E)
       (iCursor K2 (.var "read") (.var "y") 54)
         (iBind K2 (.var "read") (.var "y") 54)) = true) := by
  decide +kernel

/-! ### The runs -/

private theorem runRead1 (m n : Int) :
    ∀ c, c.varEnv = (cfg1 m n).varEnv →
      terminatesTo (.var "read") c c (readClo true (cfg0 m n).varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; rfl)

private theorem runRead2 (m n : Int) :
    ∀ c, c.varEnv = (cfg2 m n).varEnv →
      terminatesTo (.var "read") c c (readClo true (cfg0 m n).varEnv) := by
  intro c hc
  exact run_var (by rw [hc]; rfl)

private theorem runX (m n : Int) : terminatesTo (.var "x") (cfg1 m n) (cfg1 m n) (.num m) :=
  run_var rfl

private theorem runY (m n : Int) : terminatesTo (.var "y") (cfg2 m n) (cfg2 m n) (.num n) :=
  run_var rfl

private theorem runC1 (m n : Int) : terminatesTo C1 (cfg1 m n) (cfg1 m n) (.num m) :=
  run_readCall (runRead1 m n) (runX m n) rfl

/-! ### The steps a run reaches -/

private inductive InSet (m n : Int) : Step → Prop
  | v0 : InSet m n (V0 m n)
  | v1 : InSet m n (V1 m n)
  | v2 : InSet m n (V2 m n)
  | v3 : InSet m n (V3 m n)
  | leaf {s : Step} : noAppIte s.e = true → InSet m n s

private theorem inSet_step {m n : Int} {s s' : Step} (hs : InSet m n s) (h : SubStep s s') :
    InSet m n s' := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hD, hC1, _⟩ := hf
  cases hs with
  | v0 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := K0) (x := "read") (e1 := readD true)
        (e2 := Q) (F := 60) (cfg := cfg0 m n) h
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl : r1 = rD := ok_inj h1 (eq_okVal hD)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 (run_readD true (cfg0 m n) rfl)
        exact InSet.v1
  | v1 =>
      obtain ⟨f, hf, h⟩ := SubStep.vlet_inv (ctx := K1) (x := "a") (e1 := C1)
        (e2 := C2) (F := 58) (cfg := cfg1 m n) h
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨r1, c1, v1, h1, hr1, rfl⟩
      · exact InSet.v2
      · obtain rfl : r1 = rC1 := ok_inj h1 (eq_okVal hC1)
        obtain ⟨rfl, rfl⟩ := terminatesTo_det hr1 (runC1 m n)
        exact InSet.v3
  | v2 =>
      exact InSet.leaf (readCall_sub (B := K1) (fe := .var "read") (arg := .var "x")
        (F := 56) (cfgB := cfg1 m n) rfl rfl (runRead1 m n) (runX m n) h)
  | v3 =>
      exact InSet.leaf (readCall_sub (B := K2) (fe := .var "read") (arg := .var "y")
        (F := 56) (cfgB := cfg2 m n) rfl rfl (runRead2 m n) (runY m n) h)
  | leaf hl => exact InSet.leaf (SubStep.noAppIte h hl)

private theorem inSet_reach {m n : Int} {s : Step} (h : Reach (V0 m n) s) : InSet m n s := by
  induction h with
  | refl => exact InSet.v0
  | tail _ hsub ih => exact inSet_step ih hsub

/-- The run makes two calls: at the step of `read x`, typed against `res1`, it
    returns `m`; at the step of `read y`, typed against `res2`, it returns `n`. -/
private theorem inSet_call {m n : Int} {s : Step} {effects : List Effect} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config} {o : Value} (hs : InSet m n s)
    (h : ExternCallAt s effects entry res cf o) :
    (s = V2 m n ∧ res = res1 ∧ o = .num m ∧ effects = []) ∨
    (s = V3 m n ∧ res = res2 ∧ o = .num n ∧ effects = []) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, _, _, hx1, hr1, hp1, hy2, hr2, hp2, _⟩ := hf
  cases hs with
  | v0 => cases h
  | v1 => cases h
  | v2 =>
      obtain ⟨hres, ho, _, heff, _⟩ := readCall_call (B := K1) (fe := .var "read")
        (arg := .var "x") (G := 54) (cfgB := cfg1 m n) (runRead1 m n) (runX m n) rfl hx1 hr1 hp1 h
      exact Or.inl ⟨rfl, hres, ho, heff⟩
  | v3 =>
      obtain ⟨hres, ho, _, heff, _⟩ := readCall_call (B := K2) (fe := .var "read")
        (arg := .var "y") (G := 54) (cfgB := cfg2 m n) (runRead2 m n) (runY m n) rfl hy2 hr2 hp2 h
      exact Or.inr ⟨rfl, hres, ho, heff⟩
  | leaf hl =>
      exact absurd h (ExternCallAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _))

/-- No step of the set declares an `extern val`. -/
private theorem inSet_val {m n : Int} {s : Step} {res : TypeResult} {cf : Config} {o : Value} (hs : InSet m n s) :
    ¬ ExternValAt s res cf o := by
  intro h
  cases hs with
  | leaf hl => exact ExternValAt.not_of_reach_noApp (noApp_of_noAppIte hl) (Reach.refl _) h
  | _ => cases h

/-- Both calls are reached; the first returns `m`, the second `n`; and their
    body contexts are the ones the typing gives. -/
theorem reach_calls (m n : Int) :
    (Reach (V0 m n) (V2 m n) ∧
      ∃ entry, entry.bodyCtx = iBody K1 (.var "read") (.var "x") 54 ∧
        ExternCallAt (V2 m n) [] entry res1 (cfg1 m n) (.num m)) ∧
    (Reach (V0 m n) (V3 m n) ∧
      ∃ entry, entry.bodyCtx = iBody K2 (.var "read") (.var "y") 54 ∧
        ExternCallAt (V3 m n) [] entry res2 (cfg2 m n) (.num n)) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨_, hD, hC1, hx1, hr1, hp1, hy2, hr2, hp2, _⟩ := hf
  obtain ⟨⟨hm1, hap1⟩, ⟨hm2, hap2⟩⟩ := calls_chain
  have h01 : Reach (V0 m n) (V1 m n) :=
    .tail .refl (SubStep.vletBody (c1 := cfg0 m n) (v1 := readClo true (cfg0 m n).varEnv)
      (eq_okVal hD) (run_readD true (cfg0 m n) rfl))
  refine ⟨⟨.tail h01 SubStep.vletBound,
      readCall_mk (runRead1 m n) (runX m n) rfl hx1 hr1 hp1 hm1 hap1⟩,
    ⟨.tail h01 (SubStep.vletBody (eq_okVal hC1) (runC1 m n)),
      readCall_mk (runRead2 m n) (runY m n) rfl hy2 hr2 hp2 hm2 hap2⟩⟩

/-- The first call of one run and the second call of another are not the same
    call: the expressions differ, and so do the typing contexts (the tag
    counter is 0 at the first call and 1 at the second), so the context alone
    would separate them. -/
theorem crossed_not_same (m₀ n₀ m₁ n₁ : Int) :
    (V2 m₀ n₀).e ≠ (V3 m₁ n₁).e ∧ (V2 m₀ n₀).ctx ≠ (V3 m₁ n₁).ctx := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hK1, hK2⟩ := hf
  refine ⟨by simp [V2, V3, C1, C2], fun h => ?_⟩
  have : K1.nextTag = K2.nextTag := by simpa [V2, V3] using congrArg TypeContext.nextTag h
  rw [hK1, hK2] at this
  cases this

/-! ### The premises -/

/-- *Match* holds in a run whose two outputs pass the check. -/
theorem match_of {m n : Int} (hm : 0 ≤ m) (hn : 0 ≤ n) (predSat : PredSat)
    {β : BindVals} (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β) :
    ExternCallsMatch predSat (V0 m n) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨-, -, -, -, -, -, -, -, -, ht1, ht2, hreg1, hreg2, -, -, -, -, hd0, hd1, -⟩ := hf
  refine ⟨fun s effects entry res cf o hreach hcall => ?_,
    fun _ _ _ _ hreach hv => absurd hv (inSet_val (inSet_reach hreach))⟩
  rcases inSet_call (inSet_reach hreach) hcall with ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩
  · exact callMatches_of hlaws hd0 ht1 hreg1 (by simp [hm])
  · exact callMatches_of hlaws hd1 ht2 hreg2 (by simp [hn])

/-- *Agreement* for two runs holds exactly when they start with the same `x`
    and the same `y`. -/
theorem agree_iff (m₀ n₀ m₁ n₁ : Int) :
    ExternCallsAgree (V0 m₀ n₀) (V0 m₁ n₁) ↔ m₀ = m₁ ∧ n₀ = n₁ := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨-, -, -, -, -, -, -, -, -, ht1, ht2, hreg1, hreg2, hg1, hg2, hety1, hety2, -⟩ := hf
  constructor
  · intro h
    obtain ⟨⟨hr₀, e₀, hb₀, hc₀⟩, ⟨hr₀', e₀', hb₀', hc₀'⟩⟩ := reach_calls m₀ n₀
    obtain ⟨⟨hr₁, e₁, hb₁, hc₁⟩, ⟨hr₁', e₁', hb₁', hc₁'⟩⟩ := reach_calls m₁ n₁
    refine ⟨?_, ?_⟩
    · by_contra hne
      exact callAgrees_false ht1 hg1 hreg1 hety1 (by simpa using hne)
        (h.calls _ _ _ _ _ _ _ _ _ _ hr₀ hr₁ rfl rfl rfl hc₀ hc₁ (hb₀.trans hb₁.symm))
    · by_contra hne
      exact callAgrees_false ht2 hg2 hreg2 hety2 (by simpa using hne)
        (h.calls _ _ _ _ _ _ _ _ _ _ hr₀' hr₁' rfl rfl rfl hc₀' hc₁' (hb₀'.trans hb₁'.symm))
  · rintro ⟨rfl, rfl⟩
    refine ⟨fun s₀ s₁ _ _ _ res _ _ o₀ o₁ hr₀ hr₁ _ he _ hc₀ hc₁ _ => ?_⟩
    rcases inSet_call (inSet_reach hr₀) hc₀ with ⟨rfl, -, rfl, rfl⟩ | ⟨rfl, -, rfl, rfl⟩ <;>
      rcases inSet_call (inSet_reach hr₁) hc₁ with ⟨rfl, -, rfl, -⟩ | ⟨rfl, -, rfl, -⟩
    · exact callAgrees_nil rfl
    · exact absurd he (crossed_not_same _ _ _ _).1
    · exact absurd he.symm (crossed_not_same _ _ _ _).1
    · exact callAgrees_nil rfl

/-- **Two tagged calls in each of two runs.** The typing accepts the program;
    each call allocates its own tag (0 and 1), which the policy sets true.
    *Match* holds in the runs (5, 7) and (5, 8) for every lawful `predSat`
    (and one exists). *Agreement* holds for the runs (5, 7) and (5, 7), which a
    crossed pairing of the calls would reject, and fails for the runs (5, 7)
    and (5, 8). -/
theorem two_calls_case :
    typecheck K0 prog 60 = .ok rootRes ∧
    (∀ (predSat : PredSat) (β : BindVals), PredSatLaws predSat (programTable ∅ rootRes.tagLog') β →
      ExternCallsMatch predSat (V0 5 7) ∧ ExternCallsMatch predSat (V0 5 8)) ∧
    (∀ β : BindVals, PredSatLaws geSat (programTable ∅ rootRes.tagLog') β) ∧
    ExternCallsAgree (V0 5 7) (V0 5 7) ∧
    ¬ ExternCallsAgree (V0 5 7) (V0 5 8) := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hall, -⟩ := hf
  refine ⟨eq_okVal hp, fun predSat _ hlaws =>
    ⟨match_of (by decide) (by decide) predSat hlaws,
     match_of (by decide) (by decide) predSat hlaws⟩,
    fun _ => predSatLaws_geSat (geTable_of_allGe hall), (agree_iff 5 7 5 7).2 ⟨rfl, rfl⟩, ?_⟩
  rw [agree_iff]
  decide

/-! ### The guards the run tests -/

/-- The run reaches no conditional, so the condition on the guards it tests
    holds for every view. -/
theorem tests (m n : Int) (β : BindVals) : TestsAgreeWithView β (V0 m n) := by
  refine ⟨?_⟩
  intro ctx e1 e2 e3 f cfg _ _ _ _ hreach _ _ _
  have hs := inSet_reach hreach
  generalize hst : (⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ : Step) = st at hs
  exfalso
  cases hs with
  | leaf hl => subst hst; exact noAppIte_ne_ite hl rfl
  | _ => simp [V0, V1, V2, V3, prog, Q, C1, C2] at hst

end TwoCalls

end ExternCallsWitness
