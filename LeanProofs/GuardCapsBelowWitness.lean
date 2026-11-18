/-
  GuardCapsBelowWitness.lean — a sufficient condition for `GuardCapsBelow`.

  `GuardCapsBelow ctx` (`FaultRobustness.lean`), a premise of the
  fault-robustness specification, bounds by `nextLoc` the reference locations of
  the captured environment of every guard reachable in the context
  (`GuardDescInEnvsDeep`, `CapturedEnvRefLocsFullBounded`). This module states a
  simpler condition, `GuardLocsBelow ctx`: every location named anywhere in the
  captured environment of a guard of the context (`LocInQ`, `GuardLocQ`) is
  below `nextLoc`. It proves that `GuardLocsBelow` implies `GuardCapsBelow` for
  every context (`guardCapsBelow_of_guardLocsBelow`). A cell's type always has
  `etyp = int` (`MemoryTypeEnv.lookup`), so the memory clause of `GuardLocsBelow`
  loses nothing.

  The converse fails, in two contexts where a location above `nextLoc` is named
  where `GuardCapsBelow` does not look:

  * `converse_fails`: a guard nested in the captured environment of another
    guard captures `ref {5}`; `GuardDescInEnvsDeep` does not descend into the
    captured environment of a guard;
  * `converse_fails_argQ`: a guard captures a function whose extern closure has
    the precondition `ref {5}`; `CapturedEnvRefLocsFullBounded` does not look at
    an extern closure's precondition.

  The module is a leaf of the import graph; nothing on the fault-robustness proof
  path depends on it.
-/

import LeanProofs.FaultRobustness

open Std

namespace GuardCapsBelowWitness

/-! ## Locations named in a type and in the guards of a type -/

mutual
/-- `l` is named somewhere in a qualified type. -/
inductive LocInQ (l : Loc) : QTyp → Prop
  | etyp {q : QTyp} : LocInE l q.etyp → LocInQ l q
  | pred {q : QTyp} : LocInP l q.pred → LocInQ l q
inductive LocInE (l : Loc) : ETyp → Prop
  | ref {ls : LocSet} : ls.contains l = true → LocInE l (.ref ls)
  | arrow {a b : Typ} {p : Poison} {tcls : List FnTClosure} {tcl : FnTClosure} :
      tcl ∈ tcls → LocInF l tcl → LocInE l (.arrow a b p tcls)
  | parrow {a b : Typ} {p : Poison} {tcls : List PFnTClosure} {tcl : PFnTClosure} :
      tcl ∈ tcls → LocInPF l tcl → LocInE l (.parrow a b p tcls)
inductive LocInP (l : Loc) : Predicate → Prop
  | cap {k : Tag} {x : Name} {body : PExpr} {cap : List (Name × QTyp)} {y : Name} {q : QTyp} :
      (y, q) ∈ cap → LocInQ l q → LocInP l (.guardClosure k x body cap)
inductive LocInF (l : Loc) : FnTClosure → Prop
  | regular {x : Name} {e : Expr} {env : List (Name × QTyp)} {y : Name} {q : QTyp} :
      (y, q) ∈ env → LocInQ l q → LocInF l (.regular x e env)
  | externEnv {id : ExternId} {x : Name} {r : ExternReturn} {effs : List Effect}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} {y : Name} {q : QTyp} :
      (y, q) ∈ env → LocInQ l q → LocInF l (.extern id x r effs env argQ caps)
  | externArg {id : ExternId} {x : Name} {r : ExternReturn} {effs : List Effect}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} :
      LocInQ l argQ → LocInF l (.extern id x r effs env argQ caps)
inductive LocInPF (l : Loc) : PFnTClosure → Prop
  | regular {x : Name} {e : PExpr} {env : List (Name × QTyp)} {y : Name} {q : QTyp} :
      (y, q) ∈ env → LocInQ l q → LocInPF l (.regular x e env)
  | externEnv {id : ExternId} {x : Name} {r : ExternReturn}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} {y : Name} {q : QTyp} :
      (y, q) ∈ env → LocInQ l q → LocInPF l (.extern id x r env argQ caps)
  | externArg {id : ExternId} {x : Name} {r : ExternReturn}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} :
      LocInQ l argQ → LocInPF l (.extern id x r env argQ caps)
end

mutual
/-- `l` is named in the captured environment of a guard reachable in a type:
    its own predicate, or a guard in a closure's captured environment or in an
    extern precondition. -/
inductive GuardLocQ (l : Loc) : QTyp → Prop
  | etyp {q : QTyp} : GuardLocE l q.etyp → GuardLocQ l q
  | pred {q : QTyp} : LocInP l q.pred → GuardLocQ l q
inductive GuardLocE (l : Loc) : ETyp → Prop
  | arrow {a b : Typ} {p : Poison} {tcls : List FnTClosure} {tcl : FnTClosure} :
      tcl ∈ tcls → GuardLocF l tcl → GuardLocE l (.arrow a b p tcls)
  | parrow {a b : Typ} {p : Poison} {tcls : List PFnTClosure} {tcl : PFnTClosure} :
      tcl ∈ tcls → GuardLocPF l tcl → GuardLocE l (.parrow a b p tcls)
inductive GuardLocF (l : Loc) : FnTClosure → Prop
  | regular {x : Name} {e : Expr} {env : List (Name × QTyp)} {y : Name} {q : QTyp} :
      (y, q) ∈ env → GuardLocQ l q → GuardLocF l (.regular x e env)
  | externEnv {id : ExternId} {x : Name} {r : ExternReturn} {effs : List Effect}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} {y : Name} {q : QTyp} :
      (y, q) ∈ env → GuardLocQ l q → GuardLocF l (.extern id x r effs env argQ caps)
  | externArg {id : ExternId} {x : Name} {r : ExternReturn} {effs : List Effect}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} :
      GuardLocQ l argQ → GuardLocF l (.extern id x r effs env argQ caps)
inductive GuardLocPF (l : Loc) : PFnTClosure → Prop
  | regular {x : Name} {e : PExpr} {env : List (Name × QTyp)} {y : Name} {q : QTyp} :
      (y, q) ∈ env → GuardLocQ l q → GuardLocPF l (.regular x e env)
  | externEnv {id : ExternId} {x : Name} {r : ExternReturn}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} {y : Name} {q : QTyp} :
      (y, q) ∈ env → GuardLocQ l q → GuardLocPF l (.extern id x r env argQ caps)
  | externArg {id : ExternId} {x : Name} {r : ExternReturn}
      {env : List (Name × QTyp)} {argQ : QTyp} {caps : List Capture} :
      GuardLocQ l argQ → GuardLocPF l (.extern id x r env argQ caps)
end

/-- Every location named in the captured environment of a guard reachable in the
    context is below `nextLoc`. -/
def GuardLocsBelow (ctx : TypeContext) : Prop :=
  (∀ x qt, ctx.varEnv.lookup x = some qt → ∀ l, GuardLocQ l qt → l < ctx.nextLoc) ∧
  (∀ l₀ me, ctx.memEnv.get? l₀ = some me → ∀ l, LocInP l me.pred → l < ctx.nextLoc)

/-! ## `GuardLocsBelow` implies `GuardCapsBelow` -/

/-- A location named in a guard of an inner type is named in a guard of the outer type. -/
private theorem GuardLocQ_of_QTypInQTyp {l : Loc} {qt qtRoot : QTyp}
    (h : QTypInQTyp qt qtRoot) : GuardLocQ l qt → GuardLocQ l qtRoot := by
  induction h with
  | self _ => exact id
  | in_arrow qtInner qtOuter st₁ st₂ p tcls tcl x hetyp hmem hcap =>
      intro hl
      refine GuardLocQ.etyp ?_
      rw [hetyp]
      refine GuardLocE.arrow hmem ?_
      cases tcl with
      | regular _ _ _ => exact GuardLocF.regular hcap hl
      | extern _ _ _ _ _ _ _ => exact GuardLocF.externEnv hcap hl
  | in_parrow qtInner qtOuter st₁ st₂ p tcls tcl x hetyp hmem hcap =>
      intro hl
      refine GuardLocQ.etyp ?_
      rw [hetyp]
      refine GuardLocE.parrow hmem ?_
      cases tcl with
      | regular _ _ _ => exact GuardLocPF.regular hcap hl
      | extern _ _ _ _ _ _ => exact GuardLocPF.externEnv hcap hl
  | trans qt₁ qt₂ qt₃ _ _ ih12 ih23 => exact fun hl => ih23 (ih12 hl)

/-- If every location named in the entries of `env` (`LocInQ`) is below `nl`, then
    `env` is fully ref-location bounded. -/
private theorem fullBounded_of_locs {env : List (Name × QTyp)} {nl : Loc}
    (h : ∀ y q, (y, q) ∈ env → ∀ l, LocInQ l q → l < nl) :
    CapturedEnvRefLocsFullBounded env nl := by
  intro n
  induction n generalizing env with
  | zero => trivial
  | succ n ih =>
    intro name qt hmem
    refine ⟨?_, ?_⟩
    · unfold etypRefLocsBounded
      cases hq : qt.etyp with
      | ref ls =>
          intro l hl
          exact h name qt hmem l (LocInQ.etyp (by rw [hq]; exact LocInE.ref hl))
      | _ => trivial
    · cases hq : qt.etyp with
      | arrow a b p tcls =>
          intro tcl htcl
          cases tcl with
          | regular x e env' =>
              exact ih (fun y q' hyq l hl =>
                h name qt hmem l (LocInQ.etyp (by rw [hq]; exact LocInE.arrow htcl (LocInF.regular hyq hl))))
          | extern id x r effs env' argQ caps =>
              exact ih (fun y q' hyq l hl =>
                h name qt hmem l (LocInQ.etyp (by rw [hq]; exact LocInE.arrow htcl (LocInF.externEnv hyq hl))))
      | parrow a b p tcls =>
          intro tcl htcl
          cases tcl with
          | regular x e env' =>
              exact ih (fun y q' hyq l hl =>
                h name qt hmem l (LocInQ.etyp (by rw [hq]; exact LocInE.parrow htcl (LocInPF.regular hyq hl))))
          | extern id x r env' argQ caps =>
              exact ih (fun y q' hyq l hl =>
                h name qt hmem l (LocInQ.etyp (by rw [hq]; exact LocInE.parrow htcl (LocInPF.externEnv hyq hl))))
      | _ => trivial

/-- A memory type entry has `etyp = int`, so deep inclusion in it is equality. -/
private theorem memLookup_deep {m : MemoryTypeEnv} {l₀ : Loc} {qt qtRoot : QTyp}
    (hm : m.lookup l₀ = some qtRoot) (hin : QTypInQTyp qt qtRoot) :
    ∃ me, m.get? l₀ = some me ∧ qt.pred = me.pred := by
  unfold MemoryTypeEnv.lookup at hm
  cases hg : m.get? l₀ with
  | none => rw [hg] at hm; exact absurd hm (by simp)
  | some me =>
      rw [hg] at hm
      have hm' : (⟨ETyp.int, me.poison, me.pred⟩ : QTyp) = qtRoot := Option.some.inj hm
      subst hm'
      have := QTypInQTyp_eq_of_nonFunctionTarget hin rfl
      exact ⟨me, rfl, by rw [this]⟩

theorem guardCapsBelow_of_guardLocsBelow {ctx : TypeContext}
    (h : GuardLocsBelow ctx) : GuardCapsBelow ctx := by
  intro k d hd
  cases hd with
  | intro qt k d henv hqd =>
    have hpred := qtypGuardDesc?_eq_some_pred_guardClosure hqd
    apply fullBounded_of_locs
    intro y q hyq l hl
    have hlp : LocInP l qt.pred := by rw [hpred]; exact LocInP.cap hyq hl
    cases henv with
    | inVar σ Γ x qt qtRoot hx hin =>
        exact h.1 x qtRoot hx l (GuardLocQ_of_QTypInQTyp hin (GuardLocQ.pred hlp))
    | inMem σ Γ l₀ qt qtRoot hm hin =>
        obtain ⟨me, hme, hpe⟩ := memLookup_deep hm hin
        exact h.2 l₀ me hme l (by rw [← hpe]; exact hlp)

/-! ## The converse fails: a guard nested in a guard -/

/-- `z : ref {5}`, the innermost captured entry. -/
def innerQ : QTyp := ⟨.ref (LocSet.singleton 5), false, .noPred⟩
/-- An `int` carrying a guard `@1` that captures `z : ref {5}`. -/
def midQ : QTyp := ⟨.int, false, .guardClosure 1 "b" (.bool true) [("z", innerQ)]⟩
/-- An `int` carrying a guard `@0` that captures `y : midQ`. -/
def outerQ : QTyp := ⟨.int, false, .guardClosure 0 "a" (.bool true) [("y", midQ)]⟩

/-- One variable `x : outerQ`, no cells, `nextLoc = 0`. -/
def ctxB : TypeContext :=
  { pc := false, regime := {}, memEnv := {}, varEnv := (({} : VarTypeEnv).insert "x" outerQ),
    tagEnv := {}, nextLoc := 0, nextTag := 2, pureCtx := false }

private theorem ctxB_lookup : ctxB.varEnv.lookup "x" = some outerQ := by
  simp [ctxB, VarTypeEnv.lookup]

private theorem ctxB_lookup_inv {x : Name} {qt : QTyp} (h : ctxB.varEnv.lookup x = some qt) :
    qt = outerQ := by
  simp only [ctxB, VarTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert,
    ExtTreeMap.getElem?_empty] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)


private theorem ctxB_lookup_inv_mem {l : Loc} {qt : QTyp} (h : ctxB.memEnv.lookup l = some qt) : False := by
  simp [ctxB, MemoryTypeEnv.lookup] at h

/-- `GuardCapsBelow` holds at `ctxB` (nextLoc = 0): the only reachable guard is `@0`,
    which captures `y : midQ`, an `int`; the `ref {5}` sits in the predicate of `midQ`. -/
theorem ctxB_capsBelow : GuardCapsBelow ctxB := by
  intro k d hd
  cases hd with
  | intro qt k d henv hqd =>
    cases henv with
    | inVar σ Γ x qt qtRoot hx hin =>
        have h1 := ctxB_lookup_inv hx
        subst h1
        have h2 := QTypInQTyp_eq_of_nonFunctionTarget hin rfl
        subst h2
        simp only [qtypGuardDesc?, outerQ, Option.some.injEq, Prod.mk.injEq] at hqd
        obtain ⟨rfl, rfl⟩ := hqd
        intro n
        cases n with
        | zero => trivial
        | succ n =>
            intro name q hmem
            simp only [List.mem_singleton, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl⟩ := hmem
            exact ⟨trivial, trivial⟩
    | inMem σ Γ l₀ qt qtRoot hm hin => exact (ctxB_lookup_inv_mem hm).elim

/-- `GuardLocsBelow` fails at `ctxB`: the guard `@1`, nested in the predicate of the
    entry `y`, names location 5, which is not below `nextLoc = 0`. -/
theorem ctxB_not_locsBelow : ¬ GuardLocsBelow ctxB := by
  intro h
  have h5 : 5 < ctxB.nextLoc :=
    h.1 "x" outerQ ctxB_lookup 5
      (GuardLocQ.pred (LocInP.cap (y := "y") (q := midQ) (by simp)
        (LocInQ.pred (LocInP.cap (y := "z") (q := innerQ) (by simp)
          (LocInQ.etyp (LocInE.ref (by simp [LocSet.singleton])))))))
  simp [ctxB] at h5

theorem converse_fails : GuardCapsBelow ctxB ∧ ¬ GuardLocsBelow ctxB :=
  ⟨ctxB_capsBelow, ctxB_not_locsBelow⟩


/-! ## The converse fails: an extern closure's precondition -/

/-- The precondition of an extern closure: a reference to location 5. -/
def argQD : QTyp := ⟨.ref (LocSet.singleton 5), false, .noPred⟩
/-- A function type with one extern closure (empty captured environment) whose `argQ` is `argQD`. -/
def fQ : QTyp :=
  ⟨.arrow .int .int false
      [FnTClosure.extern 0 "a" (.simple .int false .noPred) [] [] argQD []], false, .noPred⟩
/-- An `int` carrying a guard `@0` that captures `f : fQ`. -/
def outerD : QTyp := ⟨.int, false, .guardClosure 0 "a" (.bool true) [("f", fQ)]⟩

def ctxD : TypeContext :=
  { pc := false, regime := {}, memEnv := {}, varEnv := (({} : VarTypeEnv).insert "x" outerD),
    tagEnv := {}, nextLoc := 0, nextTag := 1, pureCtx := false }

private theorem ctxD_lookup : ctxD.varEnv.lookup "x" = some outerD := by
  simp [ctxD, VarTypeEnv.lookup]

private theorem ctxD_lookup_inv {x : Name} {qt : QTyp} (h : ctxD.varEnv.lookup x = some qt) :
    qt = outerD := by
  simp only [ctxD, VarTypeEnv.lookup, ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert,
    ExtTreeMap.getElem?_empty] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

private theorem ctxD_lookup_inv_mem {l : Loc} {qt : QTyp} (h : ctxD.memEnv.lookup l = some qt) : False := by
  simp [ctxD, MemoryTypeEnv.lookup] at h

theorem ctxD_capsBelow : GuardCapsBelow ctxD := by
  intro k d hd
  cases hd with
  | intro qt k d henv hqd =>
    cases henv with
    | inVar σ Γ x qt qtRoot hx hin =>
        have h1 := ctxD_lookup_inv hx
        subst h1
        have h2 := QTypInQTyp_eq_of_nonFunctionTarget hin rfl
        subst h2
        simp only [qtypGuardDesc?, outerD, Option.some.injEq, Prod.mk.injEq] at hqd
        obtain ⟨rfl, rfl⟩ := hqd
        intro n
        cases n with
        | zero => trivial
        | succ n =>
            intro name q hmem
            simp only [List.mem_singleton, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl⟩ := hmem
            refine ⟨trivial, ?_⟩
            intro tcl htcl
            simp only [List.mem_singleton] at htcl
            subst htcl
            exact fullBounded_of_locs (env := []) (by simp) n
    | inMem σ Γ l₀ qt qtRoot hm hin => exact (ctxD_lookup_inv_mem hm).elim

theorem ctxD_not_locsBelow : ¬ GuardLocsBelow ctxD := by
  intro h
  have hc : (LocSet.singleton 5).contains 5 = true := by simp [LocSet.singleton]
  have hq : LocInQ 5 argQD := LocInQ.etyp (q := argQD) (LocInE.ref (ls := LocSet.singleton 5) hc)
  have hf : LocInF 5 (FnTClosure.extern 0 "a" (.simple .int false .noPred) [] [] argQD []) :=
    LocInF.externArg hq
  have hmem : FnTClosure.extern 0 "a" (.simple .int false .noPred) [] [] argQD [] ∈
      [FnTClosure.extern 0 "a" (.simple .int false .noPred) [] [] argQD []] := by simp
  have he : LocInE 5 fQ.etyp := LocInE.arrow hmem hf
  have h5 : 5 < ctxD.nextLoc :=
    h.1 "x" outerD ctxD_lookup 5
      (GuardLocQ.pred (LocInP.cap (y := "f") (q := fQ) (by simp) (LocInQ.etyp he)))
  simp [ctxD] at h5

theorem converse_fails_argQ : GuardCapsBelow ctxD ∧ ¬ GuardLocsBelow ctxD :=
  ⟨ctxD_capsBelow, ctxD_not_locsBelow⟩

end GuardCapsBelowWitness
