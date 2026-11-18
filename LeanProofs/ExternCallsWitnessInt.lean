import LeanProofs.ExternCallsWitnessBase
import LeanProofs.FaultRobustnessProofs

/-!
# A trusted entry for an `extern val` whose guard reads a `let`-bound integer

`@250` is an extern value whose guard compares the value with the variable
`lo`:

    extern val @250 : (int :> poisoned { 0, v => v >= lo })

The guard captures `lo`, a clean `int` with a binding number. A conditional
`y >= lo` that tests the declared value against the same `lo` (the same
binding number) is matched to the guard's tag.

This module gives a trusted entry for `@250` whose implementation is the
value `m`, and applies the top-level theorem to

    let lo = 3 in
    let y = extern val @250 : (int :> poisoned { 0, v => v >= lo }) in
    if y >= lo then 1 else x

typed in a context with a poisoned integer `x` and every tag of `@250`
assigned true (`polT`). The guard is matched, the regime assigns its tag
true, and the program is typed as a clean `int`.

* The entry. `lo_declSingle` and `lo_declFR` are the declaration contracts of
  `loDecl` with the implementation `loImpl m`, proved from the premise *match*
  on the declared value (`ValMatches`); `loSpec` collects them with the call
  contracts (no call is typed against a declaration of kind `val`) and
  operational safety, and `loReg` is the trusted registry that holds `@250`
  alone. The contracts hold in every context that types the declaration,
  whatever `lo` is bound to there: the guard is resolved over the whole
  environment.
* The relation `loSat β`: the checked value is a number at least the value
  the view `β` gives the binding number of `lo`. `loSat_lawful`: it satisfies
  the laws on the table of the program under every view. `loSat_lawful_cap`:
  the same on `loTmOf cap`, the table of the guard over any captured
  environment `cap` that holds `lo` as a clean integer with number 1.
* The view `βm m` of a run gives `lo` (number 1) the value 3 and `y`
  (number 2) the value `m`. `tests`: every run agrees with it at the
  conditional. `view_needed`: a view that gives number 1 another value does
  not.
* `pin_lo`: a relation that satisfies the laws on the table under a view
  that gives `lo` the value `c` holds at the guard's tag on an integer `n`
  exactly when `c ≤ n`. `match_iff_lawful`: for such a relation, with
  `c = 3`, *match* holds in a run exactly when `3 ≤ m`; `match_iff` is the
  case of `loSat (βm m)`. `agree`: *agreement* holds for every pair of runs,
  which make no extern call. `pin_lo_cap`: the pin on `loTmOf cap`, for a
  `cap` with which `y >= lo` is matched to the guard (`pinSelectsOf`).
* `same_return`: when `3 ≤ m`, two runs from any `x` return the same value.
  `true_5`: the registry holds 5; the runs from `x = 0` and `x = 1` return 1.
  `no_premises_lt`: when `m < 3`, no relation and view meet the laws on the
  table, the tests premise and *match* in a run. `fails_0`: the registry
  holds 0; the runs from `x = 0` and `x = 1` return 0 and 1.

Limits. The proofs of the entry are specific to `@250`: one guard, on an
`int`. The runs differ only in `x`.
-/

open Std LeanPoison

namespace ExternCallsWitness

namespace IntGuard

/-! ## The guard, the relation and the law -/

/-- The binding number of `lo` where the guard is made. -/
def loNum : Nat := 1

/-- A clean integer without guard. -/
def intQt : QTyp := { etyp := ETyp.int, poison := false, pred := Predicate.noPred }

/-- The body `v >= lo`. -/
def loBody : PExpr := PExpr.op (PExpr.var "v") Op.gte (PExpr.var "lo")

/-- The captured environment of the guard: `lo` with number 1 and `x` without
    a number. -/
def loCap : CapturedVarEnv := [("lo", intQt, loNum), ("x", pInt, 0)]

def loDesc : GuardDesc := { argName := "v", body := loBody, capEnv := loCap }

/-- The table of the program: tag `0` is the guard `v >= lo`. -/
def loTm : TagMeaning := (∅ : TagMeaning).update 0 loDesc

/-- The table whose tag `0` is the guard `v >= lo` over the captured
    environment `cap`; `loTm` is the table over `loCap`. -/
def loTmOf (cap : CapturedVarEnv) : TagMeaning :=
  (∅ : TagMeaning).update 0 { argName := "v", body := loBody, capEnv := cap }

/-- The relation under the view `β`: the checked value is a number at least
    the value `β` gives the binding number of `lo`. -/
def loSat (β : BindVals) : PredSat := fun _ _ v =>
  ∃ m n : Int, β loNum = some (Value.num m) ∧ v = Value.num n ∧ m ≤ n

private theorem loTmOf_lookup_eq {cap : CapturedVarEnv} {k : Tag} {d : GuardDesc}
    (h : (loTmOf cap).lookup k = some d) :
    d = { argName := "v", body := loBody, capEnv := cap } := by
  by_cases hk : (0 : Tag) = k
  · subst hk
    simpa [loTmOf, TagMeaning.lookup, TagMeaning.update] using h.symm
  · simp [loTmOf, TagMeaning.lookup, TagMeaning.update, hk] at h

/-- The argument `v`, with the variable `x` substituted, is `x`. -/
private theorem eq_var_arg {pe : PExpr} {env1 env2 : CapturedVarEnv} {x : Name} :
    ∀ {fuel : Nat},
      PExpr.equalWithEnvs (PExpr.var "v") env1 pe env2 (some ("v", PExpr.var x)) fuel = true →
      pe = PExpr.var x := by
  intro fuel h
  cases fuel with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ fuel =>
      by_cases hx : x = "v"
      · subst hx
        cases pe <;> simp_all [PExpr.equalWithEnvs, BEq.beq, beqPExpr]
      · have hbeq : (PExpr.var x == PExpr.var "v") = false := by
          simp [BEq.beq, beqPExpr, hx]
        cases fuel with
        | zero => simp [PExpr.equalWithEnvs, hbeq] at h
        | succ fuel =>
            cases pe <;> simp_all [PExpr.equalWithEnvs]

/-- The argument `v`, with `!x` substituted, is `!x`, and `x` is not `v`. -/
private theorem eq_deref_arg {env1 env2 : CapturedVarEnv} {x : Name} :
    ∀ (fuel : Nat) (pe : PExpr),
      PExpr.equalWithEnvs (PExpr.var "v") env1 pe env2
        (some ("v", PExpr.deref (PExpr.var x))) fuel = true →
      x ≠ "v" ∧ pe = PExpr.deref (PExpr.var x) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    intro pe h
    have hbeq : (PExpr.deref (PExpr.var x) == PExpr.var "v") = false := by
      simp [BEq.beq, beqPExpr]
    match fuel, ih, h with
    | 0, _, h => simp [PExpr.equalWithEnvs] at h
    | 1, _, h => simp [PExpr.equalWithEnvs, hbeq] at h
    | f + 2, ih, h =>
        cases pe with
        | deref pe' =>
            by_cases hx : x = "v"
            · subst hx
              have h' : PExpr.equalWithEnvs (PExpr.var "v") env1 pe' env2
                  (some ("v", PExpr.deref (PExpr.var "v"))) f = true := by
                simpa [PExpr.equalWithEnvs, hbeq] using h
              exact absurd rfl (ih f (by omega) pe' h').1
            · refine ⟨hx, ?_⟩
              have h' : PExpr.equalWithEnvs (PExpr.var x) env1 pe' env2
                  (some ("v", PExpr.deref (PExpr.var x))) f = true := by
                simpa [PExpr.equalWithEnvs, hbeq] using h
              cases f with
              | zero => simp [PExpr.equalWithEnvs] at h'
              | succ f =>
                  have hxv : (x == "v") = false := by simpa using hx
                  cases pe' <;> simp_all [PExpr.equalWithEnvs]
        | _ => simp [PExpr.equalWithEnvs, hbeq] at h

/-- A pure expression equal to `v >= lo` is a comparison `p1 >= p2`. -/
private theorem eq_lo_shape {env1 env2 : CapturedVarEnv} {subst : Option (Name × PExpr)}
    {pe : PExpr} {fuel : Nat}
    (h : PExpr.equalWithEnvs loBody env1 pe env2 subst fuel = true) :
    ∃ f p1 p2, fuel = f + 1 ∧ pe = PExpr.op p1 Op.gte p2 ∧
      PExpr.equalWithEnvs (PExpr.var "v") env1 p1 env2 subst f = true ∧
      PExpr.equalWithEnvs (PExpr.var "lo") env1 p2 env2 subst f = true := by
  cases fuel with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ f =>
      cases pe with
      | op p1 o p2 =>
          simp only [loBody, PExpr.equalWithEnvs, Bool.and_eq_true] at h
          obtain ⟨⟨ho, h1⟩, h2⟩ := h
          have : o = Op.gte := by
            cases o <;> first | rfl | (revert ho; decide)
          subst this
          exact ⟨f, p1, p2, rfl, rfl, h1, h2⟩
      | _ => simp [loBody, PExpr.equalWithEnvs] at h

/-- `lo`, not the argument, is compared syntactically. -/
private theorem eq_lo {env1 env2 : CapturedVarEnv} {val : PExpr} {pe : PExpr} {f : Nat}
    (h : PExpr.equalWithEnvs (PExpr.var "lo") env1 pe env2 (some ("v", val)) f = true) :
    pe = PExpr.var "lo" := by
  cases f with
  | zero => simp [PExpr.equalWithEnvs] at h
  | succ f => cases pe <;> simp_all [PExpr.equalWithEnvs]

private theorem toPExpr?_eq_var {e : Expr} {x : Name}
    (h : e.toPExpr? = some (PExpr.var x)) : e = Expr.var x := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_eq_deref_var {e : Expr} {x : Name}
    (h : e.toPExpr? = some (PExpr.deref (PExpr.var x))) : e = Expr.deref (Expr.var x) := by
  cases e with
  | deref e' =>
      cases he : e'.toPExpr? with
      | none => simp [Expr.toPExpr?, he] at h
      | some p =>
          simp [Expr.toPExpr?, he] at h
          subst h
          rw [toPExpr?_eq_var he]
  | _ => simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

private theorem toPExpr?_eq_op {e : Expr} {p1 p2 : PExpr} {o : Op}
    (h : e.toPExpr? = some (PExpr.op p1 o p2)) :
    ∃ e1 e2, e = Expr.op e1 o e2 ∧ e1.toPExpr? = some p1 ∧ e2.toPExpr? = some p2 := by
  cases e <;> simp_all [Expr.toPExpr?, Option.bind_eq_some_iff]

/-- The guard is in scope only where `lo` has the guard's binding number, when
    the captured environment `cap` holds `lo` as a clean integer with number 1. -/
private theorem scope_lo {cap : CapturedVarEnv} {S : VarTypeEnv} {B : BindEnv}
    (hq : (VarTypeEnv.ofCaptured cap).lookup "lo" = some intQt)
    (hn : (BindEnv.ofCaptured cap).get? "lo" = some loNum)
    (h : GuardInScope S B "v" loBody cap) : B.get? "lo" = some loNum := by
  rcases h.reads "lo" (by simp [loBody, PExpr.freeVars]) with
    ⟨qt, ls, l, hq', _, _, he, _⟩ | ⟨q1, q2, n1, n2, _, _, hn1, hn2, hagree, _⟩
  · rw [hq] at hq'
    cases hq'
    simp [intQt] at he
  · rw [hn] at hn1
    cases hn1
    simp only [bindNumbersAgree, loNum, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hagree
    rw [hn2, ← hagree.2]
    rfl

/-- The law holds for the relation under every view, on the table over any
    captured environment that holds `lo` as a clean integer with number 1. -/
theorem loSat_lawful_cap (gcap : CapturedVarEnv)
    (hq : (VarTypeEnv.ofCaptured gcap).lookup "lo" = some intQt)
    (hn : (BindEnv.ofCaptured gcap).get? "lo" = some loNum) (β : BindVals) :
    PredSatLaws (loSat β) (loTmOf gcap) β := by
  refine ⟨?_, ?_⟩
  · intro condition ctx fuel k deps μ ρ θ addr pm registry cfg b hwf hmatch hview hric hterm
    obtain ⟨pe, hpe, hown⟩ := matchGuard_ok_matched_owner_inScope ctx condition k deps hmatch
    rcases hown with
      ⟨x, qt, arg, body, cap, hlookup, hpred, heq, hscope⟩ |
      ⟨x, qt, ls, arg, body, cap, hlookup, hetyp, _, hne, hall, heq, hscope⟩
    · have hdeep : GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k ⟨arg, body, cap⟩ :=
        GuardDescInEnvsDeep.intro qt k ⟨arg, body, cap⟩
          (QTypInEnvs.inVar ctx.varEnv ctx.memEnv x qt qt hlookup (QTypInQTyp.self qt))
          (by simp [qtypGuardDesc?, hpred])
      have hdesc := loTmOf_lookup_eq (hwf.1 hdeep)
      simp only [GuardDesc.mk.injEq] at hdesc
      obtain ⟨rfl, rfl, rfl⟩ := hdesc
      have hloρ : ρ.lookup "lo" = β loNum :=
        hview _ hdeep "lo" (by simp [loBody, PExpr.freeVars]) loNum (scope_lo hq hn hscope)
          (by decide)
      obtain ⟨f, p1, p2, rfl, rfl, h1, h2⟩ := eq_lo_shape heq
      have hp1 := eq_var_arg h1
      have hp2 := eq_lo h2
      subst hp1 hp2
      obtain ⟨e1, e2, rfl, he1, he2⟩ := toPExpr?_eq_op hpe
      rw [toPExpr?_eq_var he1, toPExpr?_eq_var he2] at hterm
      obtain ⟨c1, v1, v2, ht1, ht2, hev, _, _⟩ := terminatesTo_op_inv' _ _ _ _ _ _ hterm
      obtain ⟨v1', hx, rfl, rfl⟩ := terminatesTo_var_inv' _ _ _ _ ht1
      obtain ⟨v2', hlo, _, rfl⟩ := terminatesTo_var_inv' _ _ _ _ ht2
      simp only at hx hlo
      cases v1 <;> cases v2 <;> simp [LeanPoison.evalOp] at hev
      rename_i n m
      subst hev
      have hβ : β loNum = some (Value.num m) := hloρ ▸ hlo
      refine ⟨Value.num n, Or.inl ⟨x, qt, "v", loBody, _, hlookup, hpred, hx⟩, ?_⟩
      constructor
      · intro hb
        exact ⟨m, n, hβ, rfl, by simpa using hb⟩
      · rintro ⟨m', n', hβ', hv, hle⟩
        rw [hβ] at hβ'
        cases hβ'
        cases hv
        simpa using hle
    · obtain ⟨l, hl⟩ : ∃ l, l ∈ ls := by
        have hlist : ls.toList.isEmpty = false := by
          rw [ExtTreeSet.isEmpty_toList]; exact hne
        cases htl : ls.toList with
        | nil => simp [htl] at hlist
        | cons a as => exact ⟨a, ExtTreeSet.mem_toList.mp (by simp [htl])⟩
      obtain ⟨memQt, hmem, hmpred⟩ := hall l hl
      have hdeep : GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k ⟨arg, body, cap⟩ :=
        GuardDescInEnvsDeep.intro memQt k ⟨arg, body, cap⟩
          (QTypInEnvs.inMem ctx.varEnv ctx.memEnv l memQt memQt hmem (QTypInQTyp.self memQt))
          (by simp [qtypGuardDesc?, hmpred])
      have hdesc := loTmOf_lookup_eq (hwf.1 hdeep)
      simp only [GuardDesc.mk.injEq] at hdesc
      obtain ⟨rfl, rfl, rfl⟩ := hdesc
      have hloρ : ρ.lookup "lo" = β loNum :=
        hview _ hdeep "lo" (by simp [loBody, PExpr.freeVars]) loNum (scope_lo hq hn hscope)
          (by decide)
      obtain ⟨f, p1, p2, rfl, rfl, h1, h2⟩ := eq_lo_shape heq
      obtain ⟨_, hp1⟩ := eq_deref_arg f p1 h1
      have hp2 := eq_lo h2
      subst hp1 hp2
      obtain ⟨e1, e2, rfl, he1, he2⟩ := toPExpr?_eq_op hpe
      rw [toPExpr?_eq_deref_var he1, toPExpr?_eq_var he2] at hterm
      obtain ⟨c1, v1, v2, ht1, ht2, hev, _, _⟩ := terminatesTo_op_inv' _ _ _ _ _ _ hterm
      obtain ⟨c1', a, n, htx, hμ, rfl, _, hvar, _, _⟩ := terminatesTo_deref_inv' _ _ _ _ ht1
      obtain ⟨vx, hx, rfl, rfl⟩ := terminatesTo_var_inv' _ _ _ _ htx
      obtain ⟨v2', hlo, _, rfl⟩ := terminatesTo_var_inv' _ _ _ _ ht2
      rw [hvar] at hlo
      simp only at hx hlo hμ
      cases v2 <;> simp [LeanPoison.evalOp] at hev
      rename_i m
      subst hev
      have hβ : β loNum = some (Value.num m) := hloρ ▸ hlo
      obtain ⟨vx', hx', hty⟩ := hric.2 hlookup
      rw [hx] at hx'
      cases hx'
      rw [hetyp] at hty
      cases hty with
      | loc hθ hin =>
        rename_i l'
        obtain ⟨memQt', hmem', hmpred'⟩ := hall l' hin
        refine ⟨Value.num n, Or.inr ⟨x, qt, memQt', ls, l', a, n, "v", loBody, _, hlookup,
          hetyp, hin, hmem', hmpred', hθ, hμ, rfl⟩, ?_⟩
        constructor
        · intro hb
          exact ⟨m, n, hβ, rfl, by simpa using hb⟩
        · rintro ⟨m', n', hβ', hv, hle⟩
          rw [hβ] at hβ'
          cases hβ'
          cases hv
          simpa using hle
  · intro _k _pred _fuel _μ _μ' _v _deps _θ _ _
    exact Iff.rfl

/-- The law holds for the relation under every view. -/
theorem loSat_lawful (β : BindVals) : PredSatLaws (loSat β) loTm β :=
  loSat_lawful_cap loCap rfl rfl β

/-! ## Consistency under the regime after the declaration

The declaration gives values to its fresh tags only. A regime that agrees
with the old one below `nextTag` keeps every fact of `consistentWithRegime`:
a guard without predicate imposes nothing, and the tag of a guard with a
predicate reachable from the environments, at any depth of closures, has an
entry in the tag meaning and is therefore below `nextTag`. -/

/-- `R'` agrees with `R` at the tag of every closure guard reachable from `qt`. -/
private def GoodIn (R R' : Regime) (qt : QTyp) : Prop :=
  ∀ qt', QTypInQTyp qt' qt → ∀ k a b c, qt'.pred = .guardClosure k a b c →
    R'.lookup? k = R.lookup? k

private theorem varsRegime_transport {predSat : PredSat} {R R' : Regime} {μ : Memory}
    {ρ : VarEnv} {e : Name × QTyp}
    (hk : ∀ k a b c, e.2.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : varsRegime predSat R μ ρ e) : varsRegime predSat R' μ ρ e := by
  cases h with
  | noPred_ok hp => exact .noPred_ok _ hp
  | guardOnly_ok k hgo => exact .guardOnly_ok _ k hgo
  | withPred_ok k a b c v bb hclos hregime hvar hcons =>
      exact .withPred_ok _ k a b c v bb hclos (by rw [hk k a b c hclos]; exact hregime) hvar hcons

private theorem locsRegime_transport {predSat : PredSat} {R R' : Regime} {μ : Memory}
    {θ : RealizationMap} {e : Loc × QTyp}
    (hk : ∀ k a b c, e.2.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : locsRegime predSat R μ θ e) : locsRegime predSat R' μ θ e := by
  cases h with
  | noPred_ok hp => exact .noPred_ok _ hp
  | guardOnly_ok k hgo => exact .guardOnly_ok _ k hgo
  | withPred_ok k a b c addr n bb hclos hregime hreal hmem hcons =>
      exact .withPred_ok _ k a b c addr n bb hclos (by rw [hk k a b c hclos]; exact hregime)
        hreal hmem hcons

/-- One level: an entry of a captured environment. -/
private theorem captured_transport {predSat : PredSat} {R R' : Regime} {μ : Memory}
    {σcap : CapturedVarEnv} {ρcap : VarEnv}
    (hgood : ∀ x qt_x, σcap.lookup x = some qt_x →
      ∀ k a b c, qt_x.pred = .guardClosure k a b c → R'.lookup? k = R.lookup? k)
    (h : capturedVarsRegimeProperty predSat R μ σcap ρcap) :
    capturedVarsRegimeProperty predSat R' μ σcap ρcap := by
  intro x qt_x k_x hlook hg hR'
  cases hp : qt_x.pred with
  | noPred => simp [qtypGuardTag, hp] at hg
  | guardOnly k => exact .guardOnly_ok _ k hp
  | guardClosure k a b c =>
      have hkx : k = k_x := by simpa [qtypGuardTag, hp] using hg
      subst hkx
      have heq := hgood x qt_x hlook k a b c hp
      have hR : R.lookup? k ≠ none := by rw [← heq]; exact hR'
      exact varsRegime_transport (fun k' a' b' c' h' => by
        rw [hp] at h'; cases h'; exact heq) (h x qt_x k hlook hg hR)

/-- A captured-environment lookup gives an entry with some binding number. -/
private theorem captured_mem {env : CapturedVarEnv} {x : Name} {qt : QTyp}
    (h : env.lookup x = some qt) : ∃ n, (x, qt, n) ∈ env := by
  simp only [CapturedVarEnv.lookup, Option.map_eq_some_iff] at h
  obtain ⟨⟨qt', n⟩, hl, rfl⟩ := h
  exact ⟨n, List_lookup_some_mem x (qt', n) env hl⟩

/-- The deep part: every nesting level of a closure value. -/
private theorem deep_transport {predSat : PredSat} {R R' : Regime} {μ : Memory}
    {θ : RealizationMap} {qt : QTyp} {v : Value}
    (hdeep : deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R μ σcap ρcap ∧
          capturedVarsTypingProperty θ σcap ρcap) qt v) :
    GoodIn R R' qt →
    deepValueQTypProperty (fun σcap ρcap =>
        capturedVarsRegimeProperty predSat R' μ σcap ρcap ∧
          capturedVarsTypingProperty θ σcap ρcap) qt v := by
  induction hdeep with
  | nonClosure hv hpe => intro _; exact .nonClosure hv hpe
  | closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem hPT _hrec hbody ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => (captured_mem hs).elim fun _ hn =>
          QTypInQTyp.in_arrow qt_x _ st1 st2 p tcls _ x hetyp hmem (by simpa [fnCapturedEnv] using
            hn)
      refine .closure xp body ρcap σcap st1 st2 p tcls hval hetyp hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs)))) hbody
  | closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem hPT _hrec ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => (captured_mem hs).elim fun _ hn =>
          QTypInQTyp.in_arrow qt_x _ _ _ p tcls _ x hetyp hmem (by simpa [fnCapturedEnv] using hn)
      exact .closure_extern id xp y argTyp retSpec effects ρcap σcap p tcls hval hetyp hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs))))
  | peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem hPT _hrec ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => (captured_mem hs).elim fun _ hn =>
          QTypInQTyp.in_parrow qt_x _ st1 st2 p tcls _ x hetyp hmem (by simpa [pfnCapturedEnv]
            using hn)
      exact .peClosure xp body pbody ρcap σcap st1 st2 p tcls hval hetyp hpure hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs))))
  | peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem hPT _hrec ih =>
      intro hgood
      have hin : ∀ x qt_x, σcap.lookup x = some qt_x → QTypInQTyp qt_x _ :=
        fun x qt_x hs => (captured_mem hs).elim fun _ hn =>
          QTypInQTyp.in_parrow qt_x _ _ _ p tcls _ x hetyp hmem (by simpa [pfnCapturedEnv] using hn)
      exact .peClosure_extern id xp y argTyp retSpec ρcap σcap p tcls hval hetyp hmem
        ⟨captured_transport (fun x qt_x hs => hgood qt_x (hin x qt_x hs)) hPT.1, hPT.2⟩
        (fun x qt_x v_x hs hr => ih x qt_x v_x hs hr
          (fun qt' h' => hgood qt' (QTypInQTyp.trans _ _ _ h' (hin x qt_x hs))))

/-- A closure guard reachable from the environments has a tag below `nextTag`. -/
private theorem guardClosure_lt {tm : TagMeaning} {ctx : TypeContext} {qt : QTyp}
    {k : Tag} {a : Name} {b : PExpr} {c : CapturedVarEnv}
    (hwfTm : wfTagMeaningCtx tm ctx) (htmb : TagMeaningBounded tm ctx.nextTag)
    (hin : QTypInEnvs qt ctx.varEnv ctx.memEnv) (hp : qt.pred = .guardClosure k a b c) :
    k < ctx.nextTag := by
  rcases hwfTm with ⟨h⟩
  exact htmb k _ (h (GuardDescInEnvsDeep.intro qt k { argName := a, body := b, capEnv := c } hin
    (by simp [qtypGuardDesc?, hp])))

/-- Consistency of the context moves to a regime that agrees with the old one
    below `nextTag`, given the tag meaning of the context. -/
private theorem consistentWithRegime_of_agreeBelow {predSat : PredSat} {R R' : Regime}
    {ctx : TypeContext} {μ : Memory} {ρ : VarEnv} {θ : RealizationMap} {tm : TagMeaning}
    (hwfTm : wfTagMeaningCtx tm ctx) (htmb : TagMeaningBounded tm ctx.nextTag)
    (hbelow : ∀ k, k < ctx.nextTag → R'.lookup? k = R.lookup? k)
    (h : consistentWithRegime predSat R ctx μ ρ θ) :
    consistentWithRegime predSat R' ctx μ ρ θ := by
  obtain ⟨hm, hv, hc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro l qt k hlookup hguard hR'
    cases hp : qt.pred with
    | noPred => simp [qtypGuardTag, hp] at hguard
    | guardOnly k' => exact .guardOnly_ok _ k' hp
    | guardClosure k' a b c =>
        have hkk : k' = k := by simpa [qtypGuardTag, hp] using hguard
        subst hkk
        have hlt := guardClosure_lt hwfTm htmb
          (QTypInEnvs.inMem _ _ l qt qt hlookup (QTypInQTyp.self qt)) hp
        have heq := hbelow k' hlt
        exact locsRegime_transport (fun k'' a' b' c' h' => by
            rw [hp] at h'; cases h'; exact heq)
          (hm l qt k' hlookup hguard (by rw [← heq]; exact hR'))
  · intro x qt k hlookup hguard hR'
    cases hp : qt.pred with
    | noPred => simp [qtypGuardTag, hp] at hguard
    | guardOnly k' => exact .guardOnly_ok _ k' hp
    | guardClosure k' a b c =>
        have hkk : k' = k := by simpa [qtypGuardTag, hp] using hguard
        subst hkk
        have hlt := guardClosure_lt hwfTm htmb
          (QTypInEnvs.inVar _ _ x qt qt hlookup (QTypInQTyp.self qt)) hp
        have heq := hbelow k' hlt
        exact varsRegime_transport (fun k'' a' b' c' h' => by
            rw [hp] at h'; cases h'; exact heq)
          (hv x qt k' hlookup hguard (by rw [← heq]; exact hR'))
  · intro x qt v hlookup hρ
    obtain ⟨hdeep⟩ := hc x qt v hlookup hρ
    exact ⟨deep_transport hdeep (fun qt' hin k a b c hp =>
      hbelow k (guardClosure_lt hwfTm htmb (QTypInEnvs.inVar _ _ x qt' qt hlookup hin) hp))⟩

/-! ## The entry -/

/-- The guard `v => v >= lo` as written. -/
def loGuard : SyntaxPredicate :=
  SyntaxPredicate.guardClosure ⟨0⟩ "v" (Expr.op (Expr.var "v") Op.gte (Expr.var "lo"))

/-- `extern val @250 : (int :> poisoned { 0, v => v >= lo })`. -/
def loDecl : ExternDeclaration :=
  { id := 250, kind := .val, typ := .int, argName := none, retSpec := none,
    effects := [], preds := [loGuard], argPoison := false }

/-- The implementation: the value `n`. -/
def loImpl (n : Int) : ExternImpl := .val (.num n)

/-- The tag mapping of the declaration at cursor `c`: index 0 gets `c`. -/
private def loMap (c : Tag) : TagMapping := (∅ : TagMapping).insert ⟨0⟩ c

private theorem lo_alloc (c : Tag) :
    collectAndAllocExternTags [loGuard] c = .ok (loMap c, c + 1) := by
  rfl

private theorem lo_log (env : VarTypeEnv) (binds : BindEnv) (c : Tag) :
    ∃ a ∈ externTagLog [loGuard] env binds (loMap c), a.tag = c := by
  simp [externTagLog, loGuard, loMap]
  exact ⟨_, rfl, rfl⟩

/-- Whatever `lo` is bound to, the guard resolves to a closure guard with the
    fresh tag: the guard captures the whole environment. -/
private theorem lo_resolve {env : VarTypeEnv} {binds : BindEnv} {c : Tag} {rp : Predicate}
    (h : resolveSyntaxPred loGuard env binds (loMap c) = .ok rp) :
    ∃ arg body cap, rp = .guardClosure c arg body cap := by
  have hget : (loMap c).get? ⟨0⟩ = some c := rfl
  simp only [loGuard, resolveSyntaxPred, hget, bind, Except.bind, pure, Except.pure] at h
  cases hp : ((Expr.var "v").op Op.gte (Expr.var "lo")).toPExpr with
  | error e => simp [hp] at h
  | ok pb =>
      simp only [hp, Except.ok.injEq] at h
      exact ⟨_, _, _, h.symm⟩

private theorem loPolicy_lookup (R : Regime) (id : ExternId) (pol : ExternId → Tag → Option Bool)
    (c k : Tag) (hk : k ≠ c) :
    (applyExternRegimePolicy R id pol (loMap c)).lookup? k = R.lookup? k := by
  have hR : applyExternRegimePolicy R id pol (loMap c) =
      (match pol id c with
       | some b => match R.lookup? c with
                   | none => R.insert c b
                   | some _ => R
       | none => R) := rfl
  rw [hR]
  cases pol id c with
  | none => rfl
  | some b =>
      cases R.lookup? c with
      | none =>
          have hcmp : compare c k ≠ .eq := by
            intro h; exact hk ((Nat.compare_eq_eq).1 h).symm
          simp [Regime.lookup?, ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert, hcmp]
      | some _ => rfl

/-- What the typing of the declaration gives. -/
private structure LoFacts (ctx : TypeContext) (res : TypeResult) : Prop where
  etyp : res.qualType.etyp = .int
  poison : res.qualType.poison = true
  guard : ∃ arg body cap, res.qualType.pred = .guardClosure ctx.nextTag arg body cap
  logged : ∃ a ∈ res.tagLog', a.tag = ctx.nextTag
  nextTag : res.nextTag' = ctx.nextTag + 1
  memEnv : res.memEnv' = ctx.memEnv
  nextLoc : res.nextLoc' = ctx.nextLoc
  declared : res.declared' = 250 :: ctx.declaredExternRefs
  regime : ∀ k, k ≠ ctx.nextTag → res.regime'.lookup? k = ctx.regime.lookup? k

private theorem lo_facts_of {ctx : TypeContext} {poison : Bool} {fuel : Nat} {res : TypeResult}
    (htc : typecheckExternVal ctx 250 .int poison loGuard fuel = .ok res) : LoFacts ctx res := by
  obtain ⟨hpz, tagMapping, nextTag', rp, ⟨qt, ctx'⟩, halloc, hres, hsurf, rfl⟩ :=
    typecheckExternVal_ok_shape htc
  rw [lo_alloc] at halloc
  simp only [Except.ok.injEq, Prod.mk.injEq] at halloc
  obtain ⟨rfl, rfl⟩ := halloc
  have hp : poison = true := by
    cases poison with
    | true => rfl
    | false => have h := hpz rfl; simp [loGuard] at h
  subst hp
  simp only [surfaceSpecToQTyp, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at hsurf
  obtain ⟨rfl, rfl⟩ := hsurf
  obtain ⟨arg, body, cap, hrp⟩ := lo_resolve hres
  exact ⟨rfl, rfl, ⟨arg, body, cap, hrp⟩, lo_log _ _ _, rfl, rfl, rfl, rfl,
    fun k hk => loPolicy_lookup _ _ _ _ _ hk⟩

/-- The typing of a declaration that the entry is about. -/
private theorem lo_typed {postExpr : Expr} {ctx : TypeContext} {res : TypeResult}
    (htyped : ExternBoundaryTyping.Decl loDecl postExpr ctx res) :
    ∃ (fuel : Nat) (poison : Bool),
      typecheck ctx postExpr (fuel + 1) = .ok res ∧
      typecheckExternVal ctx 250 .int poison loGuard fuel = .ok res := by
  cases htyped with
  | val htc =>
      rename_i fuel poison
      cases fuel with
      | zero => simp [typecheck, typecheckExpr] at htc
      | succ f => exact ⟨f, poison, htc, by simpa [typecheck, typecheckExpr] using htc⟩

private theorem lo_run {n : Int} {ctx : TypeContext} {res : TypeResult} {cᵢ cf : Config}
    {o : Value} (h : ExternDeclBoundaryRun loDecl (loImpl n) ctx res cᵢ cf o) :
    cf = cᵢ ∧ o = .num n := by
  cases h with
  | val f =>
      obtain ⟨v, hv, ho⟩ := f.impl_value
      simp only [loImpl, ExternImpl.val.injEq] at hv
      exact ⟨f.output_config, by rw [ho, ← hv]⟩
  | ref f => have h := f.kind_ref; simp [loDecl] at h
  | fn f => have h := f.kind_fn; simp [loDecl] at h
  | pfn f => have h := f.kind_pfn; simp [loDecl] at h

/-! ## Moving the context facts to the context after the declaration -/

private theorem consistent_envs {predSat : PredSat} {R : Regime} {ctx ctx' : TypeContext}
    {μ : Memory} {ρ : VarEnv} {θ : RealizationMap}
    (hm : ctx'.memEnv = ctx.memEnv) (hv : ctx'.varEnv = ctx.varEnv)
    (h : consistentWithRegime predSat R ctx μ ρ θ) :
    consistentWithRegime predSat R ctx' μ ρ θ := by
  unfold consistentWithRegime; rw [hm, hv]; exact h

private theorem agree_envs {predSat₀ predSat₁ : PredSat} {R : Regime} {ctx ctx' : TypeContext}
    {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv} {θ₀ θ₁ : RealizationMap}
    (hm : ctx'.memEnv = ctx.memEnv) (hv : ctx'.varEnv = ctx.varEnv)
    (h : agreeOnClean predSat₀ predSat₁ R ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat₀ predSat₁ R ctx' μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  unfold agreeOnClean; rw [hm, hv]; exact h

private theorem runtime_envs {ctx ctx' : TypeContext} {μ : Memory} {ρ : VarEnv}
    {θ : RealizationMap}
    (hm : ctx'.memEnv = ctx.memEnv) (hv : ctx'.varEnv = ctx.varEnv)
    (h : runtimeInstantiatesCtx ctx μ ρ θ) : runtimeInstantiatesCtx ctx' μ ρ θ := by
  unfold runtimeInstantiatesCtx; rw [hm, hv]; exact h

namespace LoFacts

variable {ctx : TypeContext} {res : TypeResult}

private theorem memEnv_after (hf : LoFacts ctx res) : (ctxAfter ctx res).memEnv = ctx.memEnv :=
  hf.memEnv

private theorem varEnv_after (_hf : LoFacts ctx res) : (ctxAfter ctx res).varEnv = ctx.varEnv :=
  rfl

private theorem below (hf : LoFacts ctx res) :
    ∀ k, k < ctx.nextTag → res.regime'.lookup? k = ctx.regime.lookup? k :=
  fun k hk => hf.regime k (Nat.ne_of_lt hk)

private theorem guard_mem (hf : LoFacts ctx res) :
    ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k := by
  intro k hk
  obtain ⟨arg, body, cap, hp⟩ := hf.guard
  have : k = ctx.nextTag := by simp [qtypGuardTag, hp] at hk; exact hk.symm
  subst this
  exact hf.logged

private theorem notfun (hf : LoFacts ctx res) : res.qualType.etyp.isFunctionType = false := by
  rw [hf.etyp]; rfl

private theorem notref (hf : LoFacts ctx res) : ¬ ∃ ls, res.qualType.etyp = ETyp.ref ls := by
  rw [hf.etyp]; rintro ⟨_, h⟩; cases h

private theorem wfCtx (hf : LoFacts ctx res) (hwf : wfTypeContext ctx) :
    wfTypeContext (ctxAfter ctx res) := by
  unfold wfTypeContext
  simp only [ctxAfter, hf.memEnv, hf.nextLoc]
  exact hwf

end LoFacts

/-- Agreement moves to the regime after the declaration. -/
private theorem agree_regime {ctx : TypeContext} {R' : Regime} (htb : TagBoundedCtx ctx)
    (hmono : Regime.monotoneStepExt ctx.regime R' (fun k => ctx.nextTag ≤ k))
    {predSat₀ predSat₁ : PredSat} {μ₀ μ₁ : Memory} {ρ₀ ρ₁ : VarEnv} {θ₀ θ₁ : RealizationMap}
    (hagree : agreeOnClean predSat₀ predSat₁ ctx.regime ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁) :
    agreeOnClean predSat₀ predSat₁ R' ctx μ₀ ρ₀ θ₀ μ₁ ρ₁ θ₁ := by
  refine ⟨fun l qt hl hclean' => ?_, fun x qt hx hclean' => ?_⟩
  · have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hmono (fun _ hk => hk)
        (TagBoundedCtx_memEnv_predTagBounded htb hl) hclean'
    cases hagree.1 l qt hl hclean0 with
    | agree_values _ _ a₀ a₁ n₀ n₁ h0 h1 h2 h3 hv =>
        refine agreeLocUnder.agree_values l qt a₀ a₁ n₀ n₁ h0 h1 h2 h3 ?_
        have hb : etypClosuresFullBounded qt.etyp ctx.nextTag := by
          rw [memEnv_lookup_etyp_int ctx.memEnv l qt hl]; trivial
        exact agreeValueUnder_clean_transport_by_cleanBack_ext hmono (fun _ hk => hk) hb
          hclean' hv
    | both_unrealized _ _ h0 h1 => exact agreeLocUnder.both_unrealized l qt h0 h1
  · have hclean0 : qtypCleanUnder ctx.regime qt :=
      cleanUnder_of_monotoneExt hmono (fun _ hk => hk)
        (TagBoundedCtx_varEnv_predTagBounded htb hx) hclean'
    cases hagree.2 x qt hx hclean0 with
    | agree_values _ _ v₀ v₁ h0 h1 hv =>
        refine agreeVarUnder.agree_values x qt v₀ v₁ h0 h1 ?_
        exact agreeValueUnder_clean_transport_by_cleanBack_ext hmono (fun _ hk => hk)
          (TagBoundedCtx_varEnv_etypClosures htb hx) hclean' hv
    | both_none _ _ h0 h1 => exact agreeVarUnder.both_none x qt h0 h1

/-- From *match*: the declared value is consistent with the regime after the
    declaration. -/
private theorem valueConsistent_of_valMatches {predSat : PredSat} {res : TypeResult}
    {cf : Config} {o : Value} {θ : RealizationMap}
    (hhinge : ∀ k, qtypGuardTag res.qualType = some k → ∃ a ∈ res.tagLog', a.tag = k)
    (hmatch : ValMatches predSat res cf o)
    (hvt : valueHasETyp θ o res.qualType.etyp)
    (hnotfun : res.qualType.etyp.isFunctionType = false) :
    valueConsistentWithRegime predSat res.regime' res.qualType cf.memory θ o := by
  have hccv : closureCapturedVarsRegime predSat res.regime' res.qualType cf.memory θ o :=
    closureCapturedVarsRegime_nonClosure_of_nonFunctionType hvt hnotfun
  cases hpred : res.qualType.pred with
  | noPred => exact .noTag (by simp [qtypGuardTag, hpred]) hccv
  | guardOnly k => exact .guardOnly_ok k hpred hccv
  | guardClosure k arg body cap =>
      have htag : qtypGuardTag res.qualType = some k := by simp [qtypGuardTag, hpred]
      obtain ⟨a, ha, hak⟩ := hhinge k htag
      cases hR : res.regime'.lookup? k with
      | none => exact .notInRegime k htag hR hccv
      | some b =>
          have hiff := hmatch a ha arg body cap b (by rw [hak]; exact hpred)
            (by rw [hak]; exact hR)
          rw [hak] at hiff
          cases b with
          | true => exact .inRegimeTrue k htag hR (.guardClosure_ok hpred (hiff.mpr rfl)) hccv
          | false =>
              refine .inRegimeFalse k htag hR ?_ hccv
              intro hholds
              cases hholds with
              | noPred_ok h => rw [hpred] at h; cases h
              | guardClosure_ok h hSat =>
                  rw [hpred] at h
                  cases h
                  exact absurd (hiff.mp hSat) (by simp)
              | guardOnly_ok h => rw [hpred] at h; cases h

/-! ## The declaration contracts -/

/-- The single-run contract: the declared value is consistent with the regime
    after the declaration by *match* (`ValMatches`). -/
theorem lo_declSingle (n : Int) : ExternDeclBoundarySingle loDecl (loImpl n) := by
  intro postExpr ctx res predSat β tm htyped _hpredlaws hframe hwfTm hTmBounded
    μ ρ θ cf o _hθwf _hwfCtx hric _hreg hcons a pm registry _hwfcfg _hreserved hrdIn hrun _hpc hvm
  obtain ⟨fuel, poison, _htc, htcV⟩ := lo_typed htyped
  have hf : LoFacts ctx res := lo_facts_of htcV
  obtain ⟨hcf, ho⟩ := lo_run hrun
  subst hcf; subst ho
  obtain ⟨tm', _tagMapping, _nextTag', _hbatch, hw, hco⟩ :=
    typecheckExternVal_canonical_batch tm ctx 250 .int poison loGuard fuel res hwfTm hTmBounded
      htcV
  have hvt : valueHasETyp θ (Value.num n) res.qualType.etyp := by
    rw [hf.etyp]; exact valueHasETyp.num _
  refine ⟨tm',
    BoundaryTagMeaningPost.of_isCanonical_predSat hco (TagFrame.laws_of_within hframe hw) hw,
    θ, ⟨fun _ _ h => h, fun h => h⟩, hvt,
    runtime_envs hf.memEnv_after hf.varEnv_after hric, ?_, ?_,
    PreservesInheritedFinalCleanLocsOneRun.refl hric, ?_, ?_⟩
  · exact consistent_envs hf.memEnv_after hf.varEnv_after
      (consistentWithRegime_of_agreeBelow hwfTm hTmBounded hf.below hcons)
  · exact valueConsistent_of_valMatches hf.guard_mem (hvm rfl) hvt hf.notfun
  · intro l qt hnc hlk _hclean
    rw [hf.memEnv] at hlk
    exact absurd (memEnv_contains_of_lookup_some _ l qt hlk) hnc
  · show ReservedDiscipline registry res.declared' θ
    rw [hf.declared]; exact ReservedDiscipline.mono_declared (fun _ hx => List.mem_cons_of_mem _ hx) hrdIn

/-- The two-run contract. *Agreement* of the declared value is proved here: the
    two runs read the same implementation, so they declare the same value. -/
theorem lo_declFR (n : Int) : ExternDeclBoundaryFR loDecl (loImpl n) := by
  intro postExpr ctx res predSat₀ predSat₁ β₀ β₁ tm htyped _hpredlaws₀ _hpredlaws₁ hframe₀
    hframe₁ hwfTm hTmBounded μ₀ μ₁ ρ₀ ρ₁ θ₀ θ₁ cf₀ cf₁ o₀ o₁ _hθ₀ _hθ₁ hwf htb hric₀ hric₁ hreg
      hcwr₀ hcwr₁ hagree
    a₀ a₁ pm registry hwfcfg₀ hwfcfg₁ _hres₀ _hres₁ hrd₀ hrd₁ hrun₀ hrun₁ hvm₀ hvm₁
  obtain ⟨fuel, poison, htc, htcV⟩ := lo_typed htyped
  have hf : LoFacts ctx res := lo_facts_of htcV
  obtain ⟨hcf₀, ho₀⟩ := lo_run hrun₀.run
  obtain ⟨hcf₁, ho₁⟩ := lo_run hrun₁.run
  subst hcf₀; subst hcf₁; subst ho₀; subst ho₁
  obtain ⟨tm', _tagMapping, _nextTag', _hbatch, hw, hco⟩ :=
    typecheckExternVal_canonical_batch tm ctx 250 .int poison loGuard fuel res hwfTm hTmBounded
      htcV
  have hpost :=
    BoundaryTagMeaningPost.of_isCanonical_predSat hco (TagFrame.laws_of_within hframe₀ hw) hw
  have hmono : Regime.monotoneStepExt ctx.regime res.regime' (fun k => ctx.nextTag ≤ k) := by
    simpa [ctxAfter] using regime_monotoneExt ctx postExpr (fuel + 1) res htc
  have hvt : ∀ θ : RealizationMap, valueHasETyp θ (Value.num n) res.qualType.etyp := by
    intro θ; rw [hf.etyp]; exact valueHasETyp.num _
  refine ⟨tm', hpost, TagFrame.laws_of_within hframe₁ hw, hpost.respectsResult, θ₀, θ₁,
    ⟨fun _ _ h => h, fun h => h⟩, ⟨fun _ _ h => h, fun h => h⟩, hvt θ₀, hvt θ₁, hpost.wfCtx,
    hf.wfCtx hwf, typecheckExpr_preserves_TagBoundedCtx ctx postExpr (fuel + 1) res htc htb,
    hwfcfg₀, hwfcfg₁,
    runtime_envs hf.memEnv_after hf.varEnv_after hric₀,
    runtime_envs hf.memEnv_after hf.varEnv_after hric₁,
    typecheckExpr_preserves_regimeConsistentWithCtx ctx postExpr (fuel + 1) res hreg htc,
    consistent_envs hf.memEnv_after hf.varEnv_after
      (consistentWithRegime_of_agreeBelow hwfTm hTmBounded hf.below hcwr₀),
    consistent_envs hf.memEnv_after hf.varEnv_after
      (consistentWithRegime_of_agreeBelow hwfTm hTmBounded hf.below hcwr₁),
    agree_envs hf.memEnv_after hf.varEnv_after (agree_regime htb hmono hagree),
    valueConsistent_of_valMatches hf.guard_mem (hvm₀ rfl) (hvt θ₀) hf.notfun,
    valueConsistent_of_valMatches hf.guard_mem (hvm₁ rfl) (hvt θ₁) hf.notfun,
    ?_, ?_, ?_⟩
  · -- Agreement: the two runs declare the same value.
    intro hclean
    cases hclean with
    | clean hp => rw [hf.poison] at hp; cases hp
    | guard k htag hR _ => exact .withPred_true_eq k htag hR hf.notfun hf.notref rfl
  · show ReservedDiscipline registry res.declared' θ₀
    rw [hf.declared]; exact ReservedDiscipline.mono_declared (fun _ hx => List.mem_cons_of_mem _ hx) hrd₀
  · show ReservedDiscipline registry res.declared' θ₁
    rw [hf.declared]; exact ReservedDiscipline.mono_declared (fun _ hx => List.mem_cons_of_mem _ hx) hrd₁

/-! ## The call contracts, operational safety and the registry -/

private theorem lo_callFR (m : Int) : ExternCallBoundaryFR loDecl (loImpl m) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ htyped₀
  cases htyped₀ with
  | fnExternMember _ hkind => simp [loDecl] at hkind
  | pfnExternMember _ hkind => simp [loDecl] at hkind

private theorem lo_callSingle (m : Int) : ExternCallBoundarySingle loDecl (loImpl m) := by
  intro _ _ _ _ _ _ _ htyped
  cases htyped with
  | fnExternMember _ hkind => simp [loDecl] at hkind
  | pfnExternMember _ hkind => simp [loDecl] at hkind

private theorem lo_operationalSafe (m : Int) : ExternOperationalSafe loDecl (loImpl m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro implFn h; simp [loImpl] at h
  · intro implPfn h; simp [loImpl] at h
  · intro v h _ _ _ _ _
    simp only [loImpl, ExternImpl.val.injEq] at h
    subst h
    exact wfValue.num m
  · intro implFn h; simp [loImpl] at h

/-- The trusted entry of `@250` with the implementation `m`. -/
theorem loSpec (m : Int) : ExternBoundarySpec loDecl (loImpl m) where
  declFR := lo_declFR m
  callFR := lo_callFR m
  declSingle := lo_declSingle m
  callSingle := lo_callSingle m
  operational := lo_operationalSafe m

/-- The trusted registry that holds the extern value alone. -/
def loReg (m : Int) : TrustedRegistry := [⟨loDecl, loImpl m, loSpec m⟩]

/-- The registry of the runs. -/
def regV (m : Int) : ExternRegistry := emptyExternRegistry.insert 250 (.val (.num m))

theorem loReg_runtime (m : Int) : (loReg m).toRuntimeRegistry = regV m := rfl

private theorem regV_noLoc {m : Int} {id : ExternId} {a : Address}
    (h : (regV m).get? id = some (.val (.loc a))) : False := by
  by_cases hid : id = 250
  · subst hid; simp [regV] at h
  · simp [regV, emptyExternRegistry, Ne.symm hid] at h

/-! ## The program -/

/-- `extern val @250 : (int :> poisoned { 0, v => v >= lo })` -/
def valD : Expr := .externVal 250 .int true loGuard

/-- The condition `y >= lo`. -/
def cond : Expr := .op (.var "y") .gte (.var "lo")

/-- `if y >= lo then 1 else x` -/
def test : Expr := .ite cond (.num 1) (.var "x")

/-- `let y = extern val @250 : ... in if y >= lo then 1 else x` -/
def body1 : Expr := .vlet "y" valD test

/-- `let lo = 3 in let y = extern val @250 : ... in if y >= lo then 1 else x` -/
def prog : Expr := .vlet "lo" (.num 3) body1

/-- Every tag of `@250` is assigned true. -/
def polT : ExternId → Tag → Option Bool := fun id _ => if id = 250 then some true else none

/-- The starting context: a poisoned integer `x`, and the assignment `polT`. -/
def K : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅, varEnv := (∅ : VarTypeEnv).update "x" pInt,
    tagEnv := ∅, nextLoc := 0, nextTag := 0, pureCtx := false, externRegime := polT }

/-- The starting state of a run from `x = n`, with the registry holding `m`. -/
def cfgX (m n : Int) : Config :=
  { memory := ∅, varEnv := VarEnv.update [] "x" (.num n), nextAddr := 0, pureMode := false,
    registry := regV m }

/-! ## The typing -/

private def rLo : TypeResult := okVal (typecheckExpr K (.num 3) 58)

/-- The context of the body of `let lo`. -/
private def K1 : TypeContext :=
  { ctxAfter K rLo with
    varEnv := K.varEnv.update "lo" rLo.qualType,
    bindEnv := K.bindEnv.insert "lo" rLo.nextBind',
    nextBind := rLo.nextBind' + 1 }

private def rV : TypeResult := okVal (typecheckExpr K1 valD 56)

/-- The context of the conditional: `y` bound to the declared value. -/
private def K2 : TypeContext :=
  { ctxAfter K1 rV with
    varEnv := K1.varEnv.update "y" rV.qualType,
    bindEnv := K1.bindEnv.insert "y" rV.nextBind',
    nextBind := rV.nextBind' + 1 }

def rootRes : TypeResult := okVal (typecheckExpr K prog 60)

private def isIntClean (q : QTyp) : Bool :=
  match q with
  | { etyp := ETyp.int, poison := false, pred := Predicate.noPred } => true
  | _ => false

private def isPInt (q : QTyp) : Bool :=
  match q with
  | { etyp := ETyp.int, poison := true, pred := Predicate.noPred } => true
  | _ => false

private theorem isIntClean_eq {q : QTyp} (h : isIntClean q = true) : q = intQt := by
  unfold isIntClean at h
  split at h
  · rfl
  · simp at h

private theorem isPInt_eq {q : QTyp} (h : isPInt q = true) : q = pInt := by
  unfold isPInt at h
  split at h
  · rfl
  · simp at h

private def capOk (cap : CapturedVarEnv) : Bool :=
  match cap with
  | [(x1, q1, n1), (x2, q2, n2)] =>
      x1 == "lo" && n1 == loNum && isIntClean q1 && x2 == "x" && n2 == 0 && isPInt q2
  | _ => false

private theorem capOk_eq {cap : CapturedVarEnv} (h : capOk cap = true) : cap = loCap := by
  unfold capOk at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨rfl, rfl, h1, rfl, rfl, h2⟩ := h
    rw [isIntClean_eq h1, isPInt_eq h2]
    rfl
  · simp at h

/-- The allocation of the guard. -/
def loAlloc : TagAlloc := { tag := 0, argName := "v", body := loBody, capEnv := loCap }

private def logOk (log : List TagAlloc) : Bool :=
  match log with
  | [a] => a.tag == 0 && a.argName == "v" && a.body == loBody && capOk a.capEnv
  | _ => false

private theorem logOk_eq {log : List TagAlloc} (h : logOk log = true) : log = [loAlloc] := by
  unfold logOk at h
  split at h
  · rename_i a
    simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    rcases a with ⟨t, an, b, c⟩
    simp only at h1 h2 h3 h4
    subst h1 h2 h3
    rw [capOk_eq h4]
    rfl
  · simp at h

private def predOk (p : Predicate) : Bool :=
  match p with
  | .guardClosure k a b c => k == 0 && a == "v" && b == loBody && capOk c
  | _ => false

private theorem predOk_eq {p : Predicate} (h : predOk p = true) :
    p = .guardClosure 0 "v" loBody loCap := by
  unfold predOk at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨rfl, rfl, rfl, h4⟩ := h
    rw [capOk_eq h4]
  · simp at h

private def selects : Bool :=
  match matchGuard cond K2.memEnv K2.varEnv K2.bindEnv 54 with
  | .ok (k, _) => k == 0
  | .error _ => false

/-- What the typing gives, as a Boolean summary evaluated by the kernel. -/
private def facts : Bool :=
  isOkB (typecheckExpr K prog 60) &&
  isOkB (typecheckExpr K (.num 3) 58) &&
  isOkB (typecheckExpr K1 valD 56) &&
  (rLo.nextBind' == 1) &&
  (rV.nextBind' == 2) &&
  (rV.regime'.lookup? 0 == some true) &&
  logOk rV.tagLog' &&
  logOk rootRes.tagLog' &&
  predOk rV.qualType.pred &&
  selects &&
  (rootRes.qualType.etyp == ETyp.int) &&
  (rootRes.qualType.poison == false)

private theorem facts_ok : facts = true := by decide +kernel

private theorem facts_of :
    typecheckExpr K prog 60 = .ok rootRes ∧
    typecheckExpr K (.num 3) 58 = .ok rLo ∧
    typecheckExpr K1 valD 56 = .ok rV ∧
    rLo.nextBind' = 1 ∧ rV.nextBind' = 2 ∧
    rV.regime'.lookup? 0 = some true ∧
    rV.tagLog' = [loAlloc] ∧ rootRes.tagLog' = [loAlloc] ∧
    rV.qualType.pred = .guardClosure 0 "v" loBody loCap ∧
    selects = true ∧
    rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false := by
  have hf := facts_ok
  simp only [facts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hf
  exact ⟨eq_okVal h1, eq_okVal h2, eq_okVal h3, h4, h5, h6, logOk_eq h7, logOk_eq h8,
    predOk_eq h9, h10, h11, h12⟩

private theorem selects_of :
    ∃ deps, matchGuard cond K2.memEnv K2.varEnv K2.bindEnv 54 = .ok (0, deps) := by
  have h := facts_of.2.2.2.2.2.2.2.2.2.1
  unfold selects at h
  split at h
  · rename_i k d heq
    simp at h
    subst h
    exact ⟨d, heq⟩
  · simp at h

/-- The program is typed as a clean `int`. -/
theorem typed_clean :
    typecheck K prog 60 = .ok rootRes ∧
      rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false :=
  ⟨facts_of.1, facts_of.2.2.2.2.2.2.2.2.2.2.1, facts_of.2.2.2.2.2.2.2.2.2.2.2⟩

/-- The table of the program is `loTm`. -/
theorem programTable_eq : programTable ∅ rootRes.tagLog' = loTm := by
  rw [facts_of.2.2.2.2.2.2.2.1]
  rfl

/-! ## The runs -/

private def cfg1 (m n : Int) : Config :=
  { cfgX m n with varEnv := (cfgX m n).varEnv.update "lo" (.num 3) }

private def cfg2 (m n : Int) : Config :=
  { cfg1 m n with varEnv := (cfg1 m n).varEnv.update "y" (.num m) }

private theorem run_three (cfg : Config) : terminatesTo (.num 3) cfg cfg (.num 3) :=
  ⟨1, false, by simp [LeanPoison.beval]⟩

private theorem run_three_inv {cfg c : Config} {v : Value} (h : terminatesTo (.num 3) cfg c v) :
    c = cfg ∧ v = .num 3 :=
  terminatesTo_literal_inv' (.num 3) (.num 3) rfl cfg c v h

private theorem run_valD (m n : Int) : terminatesTo valD (cfg1 m n) (cfg1 m n) (.num m) :=
  ⟨1, false, by simp [LeanPoison.beval, valD, cfg1, cfgX, regV, valueMatchesTyp]⟩

private theorem run_valD_inv {m : Int} {cfg c : Config} {v : Value} (hreg : cfg.registry = regV m)
    (h : terminatesTo valD cfg c v) : c = cfg ∧ v = .num m := by
  obtain ⟨fuel, vb, h⟩ := h
  cases fuel with
  | zero => unfold LeanPoison.beval at h; simp at h
  | succ f =>
      simp [LeanPoison.beval, valD, hreg, regV, valueMatchesTyp] at h
      exact ⟨h.1.symm, h.2.symm⟩

/-- A run with the value `m ≥ 3` returns 1. -/
theorem run_prog_ge (m n : Int) (hm : 3 ≤ m) :
    terminatesTo prog (cfgX m n) (cfgX m n) (.num 1) := by
  refine ⟨8, false, ?_⟩
  simp [prog, body1, valD, test, cond, LeanPoison.beval, cfgX, regV, valueMatchesTyp,
    VarEnv.lookup, VarEnv.update, LeanPoison.evalOp, List.lookup, hm]

/-- A run with the value `m < 3` returns `x`. -/
theorem run_prog_lt (m n : Int) (hm : m < 3) :
    terminatesTo prog (cfgX m n) (cfgX m n) (.num n) := by
  refine ⟨8, false, ?_⟩
  simp [prog, body1, valD, test, cond, LeanPoison.beval, cfgX, regV, valueMatchesTyp,
    VarEnv.lookup, VarEnv.update, LeanPoison.evalOp, List.lookup, Int.not_le.mpr hm]

/-! ## The steps of a run -/

/-- The root step. -/
def U0 (m n : Int) : Step := ⟨K, prog, 60, cfgX m n⟩
private def U1 (m n : Int) : Step := ⟨K1, body1, 58, cfg1 m n⟩
private def U2 (m n : Int) : Step := ⟨K1, valD, 56, cfg1 m n⟩
private def U3 (m n : Int) : Step := ⟨K2, test, 56, cfg2 m n⟩

/-- Atoms and operators: no step below calls, declares or tests. -/
private def flat : Expr → Bool
  | .num _ => true
  | .var _ => true
  | .op e1 _ e2 => flat e1 && flat e2
  | _ => false

private theorem flat_step {s s' : Step} (h : SubStep s s') (hs : flat s.e = true) :
    flat s'.e = true := by
  cases h <;> simp_all [flat]

private theorem ite_step_flat {ctx : TypeContext} {e1 e2 e3 : Expr} {F : Nat} {cfg : Config}
    {s' : Step} (h : SubStep ⟨ctx, .ite e1 e2 e3, F, cfg⟩ s') (h1 : flat e1 = true)
    (h2 : flat e2 = true) (h3 : flat e3 = true) : flat s'.e = true := by
  cases h <;> assumption

private inductive InSet (m n : Int) : Step → Prop
  | u0 : InSet m n (U0 m n)
  | u1 : InSet m n (U1 m n)
  | u2 : InSet m n (U2 m n)
  | u3 : InSet m n (U3 m n)
  | leaf {s : Step} : flat s.e = true → InSet m n s

private theorem inSet_step {m n : Int} {s s' : Step} (hs : InSet m n s) (h : SubStep s s') :
    InSet m n s' := by
  obtain ⟨_, htcLo, htcV, _⟩ := facts_of
  cases hs with
  | u0 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := K) (x := "lo") (e1 := .num 3) (e2 := body1)
        (F := 60) (cfg := cfgX m n) h
      obtain rfl : f = 58 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.leaf rfl
      · obtain rfl := ok_inj htc htcLo
        obtain ⟨rfl, rfl⟩ := run_three_inv hrun
        exact InSet.u1
  | u1 =>
      obtain ⟨f, hF, h⟩ := SubStep.vlet_inv (ctx := K1) (x := "y") (e1 := valD) (e2 := test)
        (F := 58) (cfg := cfg1 m n) h
      obtain rfl : f = 56 := by omega
      rcases h with rfl | ⟨r1, c1, v1, htc, hrun, rfl⟩
      · exact InSet.u2
      · obtain rfl := ok_inj htc htcV
        obtain ⟨rfl, rfl⟩ := run_valD_inv (m := m) rfl hrun
        exact InSet.u3
  | u2 => cases h
  | u3 => exact InSet.leaf (ite_step_flat (ctx := K2) (F := 56) (cfg := cfg2 m n) h rfl rfl rfl)
  | leaf hl => exact InSet.leaf (flat_step h hl)

private theorem inSet_reach {m n : Int} {s : Step} (h : Reach (U0 m n) s) : InSet m n s := by
  induction h with
  | refl => exact InSet.u0
  | tail _ hsub ih => exact inSet_step ih hsub

private theorem reach_U2 (m n : Int) : Reach (U0 m n) (U2 m n) :=
  Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (SubStep.vletBody facts_of.2.1 (run_three (cfgX m n))))
    SubStep.vletBound

private theorem reach_U3 (m n : Int) : Reach (U0 m n) (U3 m n) :=
  Relation.ReflTransGen.tail
    (Relation.ReflTransGen.single (SubStep.vletBody facts_of.2.1 (run_three (cfgX m n))))
    (SubStep.vletBody facts_of.2.2.1 (run_valD m n))

/-- The only conditional of a run is `U3`. -/
private theorem inSet_ite {m n : Int} {s : Step} (hs : InSet m n s) {e1 e2 e3 : Expr}
    (he : s.e = .ite e1 e2 e3) : s = U3 m n := by
  cases hs with
  | u0 => simp [U0, prog] at he
  | u1 => simp [U1, body1] at he
  | u2 => simp [U2, valD] at he
  | u3 => rfl
  | leaf hl => rw [he] at hl; simp [flat] at hl

/-- A run makes no extern call. -/
private theorem inSet_call {m n : Int} {s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value} (hs : InSet m n s) :
    ¬ ExternCallAt s effects entry res cf o := by
  intro h
  cases hs with
  | leaf hl => cases h <;> simp [flat] at hl
  | _ => cases h

/-- A run declares the extern value once, at `U2`. -/
private theorem inSet_val {m n : Int} {s : Step} {res : TypeResult} {cf : Config} {o : Value}
    (hs : InSet m n s) (h : ExternValAt s res cf o) :
    res = rV ∧ cf = cfg1 m n ∧ o = .num m := by
  cases hs with
  | leaf hl => cases h; simp [flat] at hl
  | u2 =>
      cases h with
      | mk htc hrun =>
          obtain rfl := ok_inj htc facts_of.2.2.1
          obtain ⟨rfl, rfl⟩ := run_valD_inv (m := m) rfl hrun
          exact ⟨rfl, rfl, rfl⟩
  | _ => cases h

/-! ## The view and the premises -/

/-- The view of a run: number 1 (`lo`) holds 3, number 2 (`y`) holds `m`. -/
def βm (m : Int) : BindVals :=
  fun k => if k = 1 then some (.num 3) else if k = 2 then some (.num m) else none

private theorem bind_K2 : K2.bindEnv = ((∅ : BindEnv).insert "lo" 1).insert "y" 2 := by
  obtain ⟨_, _, _, hLo, hV, _⟩ := facts_of
  show (K.bindEnv.insert "lo" rLo.nextBind').insert "y" rV.nextBind' = _
  rw [hLo, hV]
  rfl

private theorem get_K2 (x : Name) : K2.bindEnv.get? x =
    if x = "y" then some 2 else if x = "lo" then some 1 else none := by
  rw [bind_K2]
  simp only [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert,
    Std.LawfulEqCmp.compare_eq_iff_eq, ExtTreeMap.getElem?_empty]
  by_cases hy : x = "y"
  · subst hy; simp
  · by_cases hl : x = "lo"
    · subst hl; simp
    · simp [hy, hl, Ne.symm hy, Ne.symm hl]

/-- At the conditional every variable with a number holds the value the view
    gives it. -/
private theorem view_U3 (m n : Int) (xs : List Name) :
    ViewAgreesOn (βm m) K2.bindEnv (cfg2 m n).varEnv xs := by
  intro x _ k hk _
  rw [get_K2] at hk
  by_cases hy : x = "y"
  · subst hy
    simp at hk
    subst hk
    simp [cfg2, cfg1, cfgX, VarEnv.lookup, VarEnv.update, βm]
  · by_cases hl : x = "lo"
    · subst hl
      simp at hk
      subst hk
      simp [cfg2, cfg1, cfgX, VarEnv.lookup, VarEnv.update, List.lookup, βm]
    · simp [hy, hl] at hk

/-- Every run agrees with its view at the guards it tests. -/
theorem tests (m n : Int) : TestsAgreeWithView (βm m) (U0 m n) where
  tests {ctx e1 e2 e3 f cfg k deps b d} hreach _ _ _ := by
    have hs := inSet_ite (inSet_reach hreach) (e1 := e1) (e2 := e2) (e3 := e3) rfl
    simp only [U3, Step.mk.injEq] at hs
    obtain ⟨rfl, _, _, rfl⟩ := hs
    exact view_U3 m n _

private theorem deep_U3 : GuardDescInEnvsDeep K2.varEnv K2.memEnv 0 loDesc := by
  have hl : K2.varEnv.lookup "y" = some rV.qualType := VarTypeEnv_lookup_update_eq _ _ _
  have hp := facts_of.2.2.2.2.2.2.2.2.1
  exact GuardDescInEnvsDeep.intro rV.qualType 0 loDesc
    (QTypInEnvs.inVar _ _ "y" _ _ hl (QTypInQTyp.self _)) (by simp [qtypGuardDesc?, hp, loDesc])

/-- The conditional is matched to the guard's tag, which the regime assigns
    true; a view that does not give number 1 the value of `lo` fails
    *TestsAgreeWithView*. -/
theorem view_needed (m n : Int) (β : BindVals) (hβ : β 1 ≠ some (.num 3)) :
    ¬ TestsAgreeWithView β (U0 m n) := by
  intro h
  obtain ⟨deps, hmatch⟩ := selects_of
  have hreg : K2.regime.lookup? 0 = some true := facts_of.2.2.2.2.2.1
  have hv := h.tests (reach_U3 m n) hmatch hreg deep_U3
  have hlo := hv "lo" (by simp [loDesc, loBody, PExpr.freeVars]) 1
    (by rw [get_K2]; simp) (by decide)
  have h3 : (cfg2 m n).varEnv.lookup "lo" = some (.num 3) := by
    simp [cfg2, cfg1, cfgX, VarEnv.lookup, VarEnv.update, List.lookup]
  rw [h3] at hlo
  exact hβ hlo.symm

/-- *Match* under `loSat (βm m)` holds exactly when `3 ≤ m`. -/
theorem match_iff (m n : Int) : ExternCallsMatch (loSat (βm m)) (U0 m n) ↔ 3 ≤ m := by
  obtain ⟨_, _, _, _, _, hreg, hlog, _, hp, _⟩ := facts_of
  constructor
  · intro h
    have hv := h.vals _ _ _ _ (reach_U2 m n) (ExternValAt.mk facts_of.2.2.1 (run_valD m n))
    have hiff := hv loAlloc (by rw [hlog]; exact List.mem_singleton_self _) "v" loBody loCap
      true hp hreg
    obtain ⟨m', n', hβ, hv', hle⟩ := hiff.2 rfl
    simp [βm, loNum] at hβ
    cases hv'
    subst hβ
    exact hle
  · intro hm
    refine ⟨fun _ _ _ _ _ _ hreach hcall => absurd hcall (inSet_call (inSet_reach hreach)),
      fun s res cf o hreach hval => ?_⟩
    obtain ⟨rfl, rfl, rfl⟩ := inSet_val (inSet_reach hreach) hval
    intro a ha _ _ _ b _ hR
    rw [hlog, List.mem_singleton] at ha
    subst ha
    have hb : b = true := by
      have hR' : rV.regime'.lookup? 0 = some b := hR
      rw [hreg] at hR'
      exact (Option.some.inj hR').symm
    subst hb
    simp only [iff_true]
    exact ⟨3, m, rfl, rfl, hm⟩

/-! ## Any lawful relation, pinned at the guard

The laws fix a relation at the guard's tag once the view gives `lo` its
value: in a context where `y` carries the guard and `lo` is a clean integer
with number 1, the conditional `y >= lo` is matched to the tag, and the law
applies to the run that gives `y` the value `n` and `lo` the value `c`. -/

/-- `y` carries the guard of tag 0 over the captured environment `cap`. -/
private def yQtOf (cap : CapturedVarEnv) : QTyp :=
  { etyp := ETyp.int, poison := true, pred := Predicate.guardClosure 0 "v" loBody cap }

/-- `y` with the guard over `cap`, `lo` a clean integer with number 1. -/
private def pinCtxOf (cap : CapturedVarEnv) : TypeContext :=
  { pc := false, regime := ∅, memEnv := ∅,
    varEnv := ((∅ : VarTypeEnv).update "lo" intQt).update "y" (yQtOf cap),
    bindEnv := (∅ : BindEnv).insert "lo" 1, tagEnv := ∅,
    nextLoc := 0, nextTag := 1, nextBind := 2, pureCtx := false }

private theorem pinCtx_lookup {cap : CapturedVarEnv} {z : Name} {q : QTyp}
    (h : (pinCtxOf cap).varEnv.lookup z = some q) :
    (z = "y" ∧ q = yQtOf cap) ∨ (z = "lo" ∧ q = intQt) := by
  simp only [pinCtxOf] at h
  by_cases hy : z = "y"
  · subst hy
    rw [VarTypeEnv_lookup_update_eq] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [VarTypeEnv_lookup_update_ne _ "y" z _ hy] at h
    by_cases hl : z = "lo"
    · subst hl
      rw [VarTypeEnv_lookup_update_eq] at h
      exact Or.inr ⟨rfl, (Option.some.inj h).symm⟩
    · rw [VarTypeEnv_lookup_update_ne _ "lo" z _ hl] at h
      simp [VarTypeEnv.lookup] at h

private theorem pinCtx_wf (cap : CapturedVarEnv) : wfTagMeaningCtx (loTmOf cap) (pinCtxOf cap) := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hdeep
  rcases hdeep with ⟨qt, k, d, hin, hdesc⟩
  cases hin with
  | inVar _ _ z _ qtRoot hlookup hinq =>
    rcases pinCtx_lookup hlookup with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have hqt : qt = yQtOf cap :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [yQtOf, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, yQtOf] at hdesc
      obtain ⟨rfl, rfl⟩ := hdesc
      rfl
    · have hqt : qt = intQt :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [intQt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, intQt] at hdesc
  | inMem _ _ l _ qtRoot hlookup hinq =>
    simp [pinCtxOf, MemoryTypeEnv.lookup] at hlookup

/-- The run: `y` holds `n`, `lo` holds `c`. -/
private def pinRho (c n : Int) : VarEnv := [("y", Value.num n), ("lo", Value.num c)]

private def pinCfg (μ : Memory) (c n : Int) : Config :=
  { memory := μ, varEnv := pinRho c n, nextAddr := 0, pureMode := false, registry := default }

private theorem pinRic (cap : CapturedVarEnv) (μ : Memory) (c n : Int) :
    runtimeInstantiatesCtx (pinCtxOf cap) μ (pinRho c n) (∅ : RealizationMap) := by
  refine ⟨?_, ?_⟩
  · intro l a h
    simp [RealizationMap.lookup] at h
  · intro x qt h
    rcases pinCtx_lookup h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Value.num n, rfl, valueHasETyp.num _⟩
    · exact ⟨Value.num c, rfl, valueHasETyp.num _⟩

/-- `matchGuard` matches `y >= lo` to tag `0` in the context where `y` carries
    the guard over `cap` and `lo` is a clean integer with number 1. -/
def pinSelectsOf (cap : CapturedVarEnv) : Bool :=
  match matchGuard cond (pinCtxOf cap).memEnv (pinCtxOf cap).varEnv (pinCtxOf cap).bindEnv 10 with
  | .ok (k, _) => k == 0
  | .error _ => false

private theorem pinSelects_ok : pinSelectsOf loCap = true := by decide +kernel

private theorem pin_matches {cap : CapturedVarEnv} (hsel : pinSelectsOf cap = true) :
    ∃ deps, matchGuard cond (pinCtxOf cap).memEnv (pinCtxOf cap).varEnv (pinCtxOf cap).bindEnv 10
      = .ok (0, deps) := by
  unfold pinSelectsOf at hsel
  split at hsel
  · rename_i k d heq
    simp at hsel
    subst hsel
    exact ⟨d, heq⟩
  · simp at hsel

private theorem pin_runs (μ : Memory) (c n : Int) :
    terminatesTo cond (pinCfg μ c n) (pinCfg μ c n) (Value.bool (decide (n ≥ c))) := by
  refine ⟨2, false, ?_⟩
  have hy : VarEnv.lookup (pinRho c n) "y" = some (Value.num n) := rfl
  have hl : VarEnv.lookup (pinRho c n) "lo" = some (Value.num c) := rfl
  simp [cond, LeanPoison.beval, LeanPoison.evalOp, pinCfg, hy, hl]

/-- The laws fix a relation at the guard's tag, on the table over any captured
    environment `cap` for which `y >= lo` is matched to the guard: under a view
    that gives `lo`'s number the value `c`, on an integer `n` it holds exactly
    when `c ≤ n`. -/
theorem pin_lo_cap (cap : CapturedVarEnv) (hsel : pinSelectsOf cap = true) {predSat : PredSat}
    {β : BindVals} {c : Int} (hlaws : PredSatLaws predSat (loTmOf cap) β)
    (hβ : β loNum = some (Value.num c)) (μ : Memory) (n : Int) :
    predSat 0 μ (Value.num n) ↔ c ≤ n := by
  obtain ⟨deps, hmatch⟩ := pin_matches hsel
  have hview : ∀ d, GuardDescInEnvsDeep (pinCtxOf cap).varEnv (pinCtxOf cap).memEnv 0 d →
      ViewAgreesOn β (pinCtxOf cap).bindEnv (pinRho c n) (PExpr.freeVars [d.argName] d.body) := by
    intro d hd
    have hdesc := loTmOf_lookup_eq ((pinCtx_wf cap).1 hd)
    subst hdesc
    intro x hx k hk _
    have hxlo : x = "lo" := by simpa [loBody, PExpr.freeVars] using hx
    subst hxlo
    have hk1 : k = 1 := by
      simp [pinCtxOf, ExtTreeMap.get?_eq_getElem?] at hk
      exact hk.symm
    subst hk1
    show _ = β loNum
    rw [hβ]
    rfl
  obtain ⟨v, hown, hiff⟩ :=
    hlaws.match_iff cond (pinCtxOf cap) 10 0 deps μ (pinRho c n) ∅ 0 false default
      (pinCfg μ c n) (decide (n ≥ c)) (pinCtx_wf cap) hmatch hview (pinRic cap μ c n)
      (pin_runs μ c n)
  have hv : v = Value.num n := by
    rcases hown with ⟨x, qt, _, _, _, hlookup, hpred, hρ⟩ |
      ⟨x, qt, _, _, _, _, _, _, _, _, hlookup, hetyp, _⟩
    · rcases pinCtx_lookup hlookup with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hl : (pinRho c n).lookup "y" = some (Value.num n) := rfl
        rw [hl] at hρ
        exact (Option.some.inj hρ).symm
      · simp [intQt] at hpred
    · rcases pinCtx_lookup hlookup with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [yQtOf] at hetyp
      · simp [intQt] at hetyp
  rw [hv] at hiff
  rw [← hiff]
  simp

/-- The laws fix a relation at the guard's tag: under a view that gives `lo`'s
    number the value `c`, on an integer `n` it holds exactly when `c ≤ n`. -/
theorem pin_lo {predSat : PredSat} {β : BindVals} {c : Int}
    (hlaws : PredSatLaws predSat loTm β) (hβ : β loNum = some (Value.num c)) (μ : Memory)
    (n : Int) : predSat 0 μ (Value.num n) ↔ c ≤ n :=
  pin_lo_cap loCap pinSelects_ok hlaws hβ μ n

/-- *Match* holds in a run, for any relation that satisfies the laws on the
    table of the program under a view that gives `lo` the value 3, exactly
    when `3 ≤ m`. -/
theorem match_iff_lawful (m n : Int) {predSat : PredSat} {β : BindVals}
    (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β)
    (hβ : β loNum = some (Value.num 3)) :
    ExternCallsMatch predSat (U0 m n) ↔ 3 ≤ m := by
  rw [programTable_eq] at hlaws
  obtain ⟨_, _, _, _, _, hreg, hlog, _, hp, _⟩ := facts_of
  have hpin := pin_lo hlaws hβ
  constructor
  · intro h
    have hv := h.vals _ _ _ _ (reach_U2 m n) (ExternValAt.mk facts_of.2.2.1 (run_valD m n))
    have hiff := hv loAlloc (by rw [hlog]; exact List.mem_singleton_self _) "v" loBody loCap
      true hp hreg
    exact (hpin _ m).1 (hiff.2 rfl)
  · intro hm
    refine ⟨fun _ _ _ _ _ _ hreach hcall => absurd hcall (inSet_call (inSet_reach hreach)),
      fun s res cf o hreach hval => ?_⟩
    obtain ⟨rfl, rfl, rfl⟩ := inSet_val (inSet_reach hreach) hval
    intro a ha _ _ _ b _ hR
    rw [hlog, List.mem_singleton] at ha
    subst ha
    have hb : b = true := by
      have hR' : rV.regime'.lookup? 0 = some b := hR
      rw [hreg] at hR'
      exact (Option.some.inj hR').symm
    subst hb
    simp only [iff_true]
    exact (hpin _ m).2 hm

/-- With the registry holding `m < 3`, no relation and view meet the laws on
    the table of the program, the tests premise and *match* in a run: a view
    that gives `lo` the value 3 fails *match*, and any other view fails the
    tests premise. -/
theorem no_premises_lt (m n : Int) (hm : m < 3) (predSat : PredSat) (β : BindVals)
    (hlaws : PredSatLaws predSat (programTable ∅ rootRes.tagLog') β)
    (htests : TestsAgreeWithView β (U0 m n)) : ¬ ExternCallsMatch predSat (U0 m n) := by
  by_cases hβ : β 1 = some (Value.num 3)
  · rw [match_iff_lawful m n hlaws hβ]
    omega
  · exact absurd htests (view_needed m n β hβ)

/-- *Agreement* holds for every pair of runs: they make no extern call. -/
theorem agree (m n₀ n₁ : Int) : ExternCallsAgree (U0 m n₀) (U0 m n₁) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hr₀ _ _ _ _ hc₀ _ _ => absurd hc₀ (inSet_call (inSet_reach hr₀))⟩

/-- The laws on the starting table `∅`. -/
theorem laws_start (β : BindVals) : PredSatLaws (loSat β) ∅ β :=
  PredSatLaws.anti_mono (fun _ _ h => by simp at h) (loSat_lawful β)

/-- The laws on the table of the program. -/
theorem laws_program (β : BindVals) :
    PredSatLaws (loSat β) (programTable ∅ rootRes.tagLog') β := by
  rw [programTable_eq]
  exact loSat_lawful β

/-! ## The other premises of the theorem -/

/-- No critical input; the scenario commits the tags of `@250`. -/
def sV : InputSpec := { locs := ∅, vars := ∅, regimeExterns := [250] }

/-- The observation: the returned integer. -/
def obsRet : ObservableSpec := { locs := ∅, retEtyp? := some .int }

/-- Every variable of `K` is a poisoned integer. -/
theorem K_vars : ∀ x qt, K.varEnv.lookup x = some qt → qt = pInt := by
  intro x qt h
  by_cases hx : x = "x"
  · subst hx
    simp only [K, VarTypeEnv_lookup_update_eq, Option.some.injEq] at h
    exact h.symm
  · simp only [K] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h

private theorem pInt_not_clean (R : Regime) : ¬ qtypCleanUnder R pInt := by
  intro h
  cases h with
  | clean hpoison => simp [pInt] at hpoison
  | guard k htag _ _ => simp [qtypGuardTag, pInt] at htag

/-- `K`'s assignment of extern tags matches `sV`. -/
theorem externRegimeMatchesK : ExternRegimeMatchesInputSpec sV K := by
  refine ⟨fun {id} hid k => ?_, fun {id} hid k => ?_⟩
  · have h : id ≠ 250 := by simpa [sV] using hid
    simp [K, polT, h]
  · simp only [sV, List.mem_singleton] at hid
    subst hid
    exact ⟨true, by simp [K, polT]⟩

private theorem trustedK (m : Int) : InitialContextTrusted (loReg m) prog K := by
  intro id d entry hreach hlookup
  cases hreach with
  | ast hp =>
      have h : id = 250 ∧ d = loDecl := by
        simp only [prog, body1, valD, test, cond] at hp
        cases hp with
        | vlet_bound h => cases h
        | vlet_body h =>
            cases h with
            | vlet_bound h => cases h; exact ⟨rfl, rfl⟩
            | vlet_body h =>
                cases h with
                | ite_cond h =>
                    cases h with
                    | op_left h => cases h
                    | op_right h => cases h
                | ite_then h => cases h
                | ite_else h => cases h
      obtain ⟨rfl, rfl⟩ := h
      simp [loReg, TrustedRegistry.lookup?] at hlookup
      obtain ⟨_, rfl⟩ := hlookup
      rfl
  | var hlk hqt =>
      have hq := K_vars _ _ hlk
      subst hq
      unfold pInt at hqt
      cases hqt

/-- `sV` is well formed. -/
theorem wfSpecV : wfInputSpec sV := by
  unfold wfInputSpec
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l qt h
    simp [sV, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · refine And.intro ?_ ?_
      · exact Std.ExtTreeMap.nodup_keys
      · intro x qt h
        simp [sV, VarTypeEnv.lookup] at h
    · intro x qt h
      simp [sV, VarTypeEnv.lookup] at h
  · intro x qt h
    simp [sV, VarTypeEnv.lookup] at h

/-- `K` matches `sV`. -/
theorem ctxMatchesK : ctxMatchesInputSpec sV K := by
  unfold ctxMatchesInputSpec
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l qt h
    simp [sV, MemoryTypeEnv.lookup] at h
  · intro x qt h
    simp [sV, VarTypeEnv.lookup] at h
  · intro l qt k h
    simp [K, MemoryTypeEnv.lookup] at h
  · refine deepVarEnvProperty.intro _ _ ?_ ?_
    · intro x qt k h htag _
      rw [K_vars x qt h] at htag
      simp [qtypGuardTag, pInt] at htag
    · intro x qt h
      rw [K_vars x qt h]
      exact deepQTypProperty.other _ _ trivial

/-- `K` is well formed. -/
theorem wfCtxK : wfTypeContext K := by
  unfold wfTypeContext
  refine And.intro ?_ (And.intro ?_ ?_)
  · intro l h
    simp [K] at h
  · intro x qt h
    rw [K_vars x qt h]
    exact trivial
  · intro x qt h
    rw [K_vars x qt h]
    exact trivial

/-- The tags of `K` are below its next tag. -/
theorem tagBoundedK : TagBoundedCtx K := by
  unfold TagBoundedCtx
  refine And.intro ?_ (And.intro (And.intro ?_ ?_) ?_)
  · intro k hk
    simp [K] at hk
  · intro x qt h
    rw [K_vars x qt h]
    exact trivial
  · intro l qt h
    simp [K, MemoryTypeEnv.lookup] at h
  · intro x qt h
    rw [K_vars x qt h]
    exact trivial

/-- `K` respects the empty table. -/
theorem wfTmK : wfTagMeaningCtx ∅ K := by
  refine EnvRespectsTagMeaning.intro ?_
  intro k d hdeep
  rcases hdeep with ⟨qt, k, d, hin, hdesc⟩
  cases hin with
  | inVar _ _ x _ qtRoot hlookup hinq =>
      have hroot := K_vars x qtRoot hlookup
      subst hroot
      have hqt : qt = pInt :=
        QTypInQTyp_eq_of_nonFunctionTarget hinq
          (by simp [pInt, ETyp.isFunctionType, ETyp.isArrow, ETyp.isParrow])
      subst hqt
      simp [qtypGuardDesc?, pInt] at hdesc
  | inMem _ _ l _ qtRoot hlookup hinq =>
      simp [K, MemoryTypeEnv.lookup] at hlookup

/-- The empty table is bounded by `K`'s next tag. -/
theorem tmBoundedK : TagMeaningBounded ∅ K.nextTag := by
  intro k d h
  simp [TagMeaning.lookup] at h

/-- `K`'s regime is well formed for `sV`. -/
theorem wfRegimeK : wfRegime K.regime sV := by
  have htags : inputSpecTags sV = [] := rfl
  refine And.intro ?_ ?_
  · intro k hk
    rw [htags] at hk
    cases hk
  · intro k hk
    simp [K, Regime.lookup?] at hk

/-- The empty realisation map is well formed. -/
theorem wfθ₀ : wfRealizationMap ∅ := by
  intro l₁ l₂ a h
  simp [RealizationMap.lookup] at h

/-- The starting configurations are well formed. -/
theorem wfCX (m n : Int) : wfConfig (cfgX m n) := by
  refine And.intro ?_ ?_
  · intro a h
    simp [cfgX] at h
  · exact wfVarEnv.cons _ _ _ (wfValue.num n) wfVarEnv.nil

/-- The registry `regV m` reserves no location. -/
theorem reservedWFV (m : Int) : RegistryReservedWF (regV m) ∅ 0 := by
  intro a ha
  obtain ⟨id, h⟩ := ha
  exact (regV_noLoc h).elim

/-- The registry `regV m` keeps the reservation discipline of `K`. -/
theorem disciplineK (m : Int) : ReservedDiscipline (regV m) K.declaredExternRefs ∅ := by
  refine And.intro ?_ ?_
  · intro id₁ id₂ a h _
    exact (regV_noLoc h).elim
  · intro id a h _ l
    exact (regV_noLoc h).elim

private theorem lookupX (n : Int) :
    (VarEnv.update [] "x" (.num n)).lookup "x" = some (.num n) := by
  simp [VarEnv.update, VarEnv.lookup]

/-- The starting variable environment from `x = n` instantiates `K`. -/
theorem instantiatesK (n : Int) :
    runtimeInstantiatesCtx K ∅ (VarEnv.update [] "x" (.num n)) ∅ := by
  refine And.intro ?_ ?_
  · intro l a h
    simp [RealizationMap.lookup] at h
  · intro x qt h
    have hq := K_vars x qt h
    subst hq
    have hx : x = "x" := by
      by_contra hx
      simp only [K] at h
      rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
      simp [VarTypeEnv.lookup] at h
    subst hx
    exact ⟨_, lookupX n, valueHasETyp.num n⟩

/-- The closures of the trusted variables at the start, from `x = n`. -/
theorem trustedInitK {predSat : PredSat} (n : Int) :
    trustedVarsClosureRegimeInit predSat K.regime sV K ∅ (VarEnv.update [] "x" (.num n)) ∅ := by
  refine trustedVarsClosureRegimeInit.intro ?_
  intro x qt v h _ hv
  have hq := K_vars x qt h
  subst hq
  have hx : x = "x" := by
    by_contra hx
    simp only [K] at h
    rw [VarTypeEnv_lookup_update_ne _ "x" x pInt hx] at h
    simp [VarTypeEnv.lookup] at h
  subst hx
  rw [lookupX n] at hv
  obtain rfl := Option.some.inj hv
  exact closureCapturedVarsRegime.intro
    (deepValueQTypProperty.nonClosure (fun _ _ _ hc => by cases hc)
      (fun _ _ _ hc => by cases hc))

/-- The starting regime is consistent with `sV`, which has no critical input. -/
theorem consistentK {predSat : PredSat} {ρ : VarEnv} :
    consistentRegimeSpec predSat K.regime sV ∅ ρ ∅ := by
  unfold consistentRegimeSpec
  have hnil : memEnvToLocQTypList sV.locs = [] := rfl
  have hnil' : sV.vars.toList = [] := rfl
  rw [hnil, hnil']
  exact ⟨trivial, trivial⟩

/-- Two runs agree on the critical inputs of `sV`: there are none. -/
theorem agreeCriticalK {predSat₀ predSat₁ : PredSat} {ρ₁ ρ₂ : VarEnv} :
    agreeOnCriticalInputsUnderRegimeSpec predSat₀ predSat₁ K.regime sV ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [sV, MemoryTypeEnv.lookup] at h
  · intro x qt h _
    simp [sV, VarTypeEnv.lookup] at h

/-- Two runs agree on the trusted inputs of `K`: its one variable is poisoned. -/
theorem agreeTrustedK {predSat₀ predSat₁ : PredSat} {ρ₁ ρ₂ : VarEnv} :
    agreeOnTrustedInputs predSat₀ predSat₁ K.regime sV K ∅ ρ₁ ∅ ∅ ρ₂ ∅ := by
  refine And.intro ?_ ?_
  · intro l qt h
    simp [K, MemoryTypeEnv.lookup] at h
  · intro x qt h _ hclean
    rw [K_vars x qt h] at hclean
    exact absurd hclean (pInt_not_clean _)

/-! ## The theorem -/

/-- **The theorem at
    `let lo = 3 in let y = extern val @250 : (int :> poisoned { 0, v => v >= lo }) in
     if y >= lo then 1 else x`**, with the registry holding `m ≥ 3`: two runs
    from any `x` return the same value. Each run has the relation
    `loSat (βm m)` and the view `βm m`. -/
theorem same_return (m : Int) (hm : 3 ≤ m) (n₀ n₁ : Int)
    {cf₀ cf₁ : Config} {o₀ o₁ : Value}
    (hr₀ : terminatesTo prog (cfgX m n₀) cf₀ o₀) (hr₁ : terminatesTo prog (cfgX m n₁) cf₁ o₁) :
    o₀ = o₁ := by
  obtain ⟨htc, hety, hpz⟩ := typed_clean
  obtain ⟨_, _, _, _, hobs⟩ :=
    TypeSystemEnforcesFaultRobustness (loReg m) prog sV obsRet K externRegimeMatchesK
      (trustedK m) wfSpecV rfl ctxMatchesK wfCtxK rfl rfl rfl tagBoundedK
      ∅ wfTmK tmBoundedK 60 rootRes htc
      (And.intro (fun et h => by
          simp only [obsRet, Option.some.injEq] at h
          subst h
          exact ⟨hety, hpz⟩)
        (fun _ _ h => by simp [obsRet, MemoryETypEnv.lookup] at h))
      ∅ ∅ _ _ ∅ ∅ 0 0 false cf₀ cf₁ o₀ o₁ (loSat (βm m)) (loSat (βm m)) (βm m) (βm m)
      (laws_start _) (laws_start _) (laws_program _) (laws_program _) wfRegimeK wfθ₀ wfθ₀
      (wfCX m n₀) (wfCX m n₁) (reservedWFV m) (reservedWFV m) (disciplineK m) (disciplineK m)
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (And.intro (fun h _ => by simp [sV] at h)
        (fun h _ => by simp [sV, VarTypeEnv.lookup] at h))
      (instantiatesK n₀) (instantiatesK n₁) (trustedInitK n₀) (trustedInitK n₁)
      consistentK consistentK ((match_iff m n₀).2 hm) ((match_iff m n₁).2 hm)
      (tests m n₀) (tests m n₁) agreeCriticalK agreeTrustedK
      (agree m n₀ n₁) hr₀ hr₁
  exact hobs.2

/-- **The registry holds 5**: the runs from `x = 0` and `x = 1` both return 1,
    and the theorem gives the same. -/
theorem true_5 :
    terminatesTo prog (cfgX 5 0) (cfgX 5 0) (.num 1) ∧
    terminatesTo prog (cfgX 5 1) (cfgX 5 1) (.num 1) ∧
    ∀ {cf₀ cf₁ : Config} {o₀ o₁ : Value},
      terminatesTo prog (cfgX 5 0) cf₀ o₀ → terminatesTo prog (cfgX 5 1) cf₁ o₁ → o₀ = o₁ :=
  ⟨run_prog_ge 5 0 (by decide), run_prog_ge 5 1 (by decide),
    fun hr₀ hr₁ => same_return 5 (by decide) 0 1 hr₀ hr₁⟩

/-- **The registry holds 0**: the program is typed as a clean `int`, the runs
    from `x = 0` and `x = 1` return 0 and 1, and in each run no relation and
    view meet the laws on the table of the program, the tests premise and
    *match*. -/
theorem fails_0 :
    typecheck K prog 60 = .ok rootRes ∧
    rootRes.qualType.etyp = .int ∧ rootRes.qualType.poison = false ∧
    terminatesTo prog (cfgX 0 0) (cfgX 0 0) (.num 0) ∧
    terminatesTo prog (cfgX 0 1) (cfgX 0 1) (.num 1) ∧
    ∀ (n : Int) (predSat : PredSat) (β : BindVals),
      PredSatLaws predSat (programTable ∅ rootRes.tagLog') β →
      TestsAgreeWithView β (U0 0 n) → ¬ ExternCallsMatch predSat (U0 0 n) := by
  obtain ⟨h1, h2, h3⟩ := typed_clean
  exact ⟨h1, h2, h3, run_prog_lt 0 0 (by decide), run_prog_lt 0 1 (by decide),
    fun n predSat β hlaws htests => no_premises_lt 0 n (by decide) predSat β hlaws htests⟩

end IntGuard

end ExternCallsWitness
