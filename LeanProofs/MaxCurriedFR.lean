import LeanProofs.ExternProofs
import LeanProofs.ExternRegimeInt

/-!
# Program-level fault-robustness for curried `max` with a nested `captures:`

The motivating end-to-end case for extern read dependencies: the inner `@11`
declares `captures: {a}` (a clean read of the outer argument `a`), reachable
through the outer `@10`'s nested return.  Both trusted boundary specs are
complete 5-field `ExternBoundarySpec`s — `builtinMax10Spec` (whose `callFR`
returns the capture-bearing `@11` closure) and `builtinMax11CapturesSpec` (whose
`callFR` reads the captured `a` cleanly) — and the trusted registry *agrees with
the reachable declarations* (`@10` with `captures = []`, `@11` with
`captures = [a]`, the latter reached via the nested return).  Composing the
agreement witness with `TypeSystemEnforcesFaultRobustness_at` discharges the
per-context trust premise and yields program-level fault-robustness.

Because the reachable `@11` declaration carries `captures = [a]`, the registry
entry that agrees with it is the strong, capture-aware `@11` spec
(`builtinMax11CapturesSpec`).
-/

open Std LeanPoison ExternProofs ExternRegimeInt

namespace MaxCurriedFR

/-- Curried-`max` declaration: outer `@10` whose nested return is `@11` with
    `captures: {a}`.  The outer `@10` has no top-level captures clause (`[]`); the
    `[a]` lives on the nested `@11` inside `builtinMax10RetSpec`. -/
def maxCurriedProg : Expr :=
  Expr.externPfn 10 "a" Typ.int false SyntaxPredicate.noPred builtinMax10RetSpec []

/-- Trusted registry: the outer `@10` and the capture-bearing inner `@11`, each
    with its complete `ExternBoundarySpec`. -/
def maxCurriedRegistry : TrustedRegistry :=
  [⟨builtinMax10Decl, builtinMax10Impl, builtinMax10Spec⟩,
   ⟨builtinMax11CapturesDecl, builtinMax11Impl, builtinMax11CapturesSpec⟩]

/-- Every declaration syntactically reachable in `maxCurriedProg` is matched by
    the registry: `@10` (the `externPfn` node, `captures = []`) and `@11` (the
    nested return, `captures = [a]` via `nestedPfn_here`). -/
private theorem maxCurried_agreesWithProgram :
    TrustedRegistryAgreesWithProgram maxCurriedProg maxCurriedRegistry := by
  intro id d entry hprog hlookup
  unfold maxCurriedProg at hprog
  cases hprog with
  | externPfn =>
      have hl : TrustedRegistry.lookup? maxCurriedRegistry 10
          = some ⟨builtinMax10Decl, builtinMax10Impl, builtinMax10Spec⟩ := by
        simp [maxCurriedRegistry, TrustedRegistry.lookup?, builtinMax10Decl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externPfn_return hret =>
      cases hret with
      | nestedPfn_here =>
          have hl : TrustedRegistry.lookup? maxCurriedRegistry 11
              = some ⟨builtinMax11CapturesDecl, builtinMax11Impl, builtinMax11CapturesSpec⟩ := by
            simp [maxCurriedRegistry, TrustedRegistry.lookup?,
              builtinMax10Decl, builtinMax11CapturesDecl]
          rw [hl] at hlookup
          cases hlookup
          rfl
      | nestedPfn_inner hret' =>
          -- The inner `@11` return is `simple int`, which carries no further
          -- nested extern, so this branch is vacuous.
          cases hret'

/-- Per-context trust premise at the canonical empty initial context. -/
private theorem maxCurried_hagrees :
    TrustedRegistryAgreesWithReachable maxCurriedProg openEmptyCtx maxCurriedRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) maxCurried_agreesWithProgram

/-- **Program-level fault-robustness for curried `max` with nested `captures:`.**
    Composing the registry-agreement witness with the top-level FR theorem yields
    the FR conclusion for the concrete `[@10, @11captures]` registry at the empty
    context. -/
theorem maxCurried_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry maxCurriedRegistry)
      maxCurriedProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at maxCurriedRegistry maxCurriedProg s obs openEmptyCtx
    maxCurried_hagrees

/-- The tests of every run of `maxCurriedProg` agree with every view: the
    declaration node has no step below it. -/
theorem maxCurried_tests (β : BindVals) (fuel : Nat) (cfg : Config) :
    TestsAgreeWithView β ⟨openEmptyCtx, maxCurriedProg, fuel, cfg⟩ :=
  testsAgreeWithView_of_leaf (fun _ h => by cases h) (fun h => by cases h)

/-! ## Fully exercised: the applied program `let m = @10 in (m 7) 2`

`maxCurried_FR` above is over the bare `@10` declaration node (it establishes
registry agreement for the reachable declarations).  The *applied* program below additionally
applies `@10` (producing the `@11` closure) and applies that to `2` — so the
generic FR theorem routes the `@11` application through the registry's
`builtinMax11CapturesSpec.callFR`, the captured-`a` cleanness gate.  The reachable
declarations are unchanged (`@10`, `@11`): the `let`-body `(m 7) 2` is
applications of a variable and numerals, which carry no extern declarations. -/

/-- Applied curried-`max`: `let m = (extern pfn @10 a … captures-bearing @11) in
    (m 7) 2`. -/
def appliedMaxCurriedProg : Expr :=
  Expr.vlet "m"
    (Expr.externPfn 10 "a" Typ.int false SyntaxPredicate.noPred builtinMax10RetSpec [])
    (Expr.app (Expr.app (Expr.var "m") (Expr.num 7)) (Expr.num 2))

/-- The reachable declarations of the applied program are exactly `@10` and `@11`,
    each matched by its registry entry.  The `let`-bound declaration reaches them
    (`@10` via `externPfn`, `@11` via the nested return `nestedPfn_here`); the
    `let`-body `(m 7) 2` reaches none (applications of `var`/`num`). -/
private theorem appliedMaxCurried_agreesWithProgram :
    TrustedRegistryAgreesWithProgram appliedMaxCurriedProg maxCurriedRegistry := by
  intro id d entry hprog hlookup
  unfold appliedMaxCurriedProg at hprog
  cases hprog with
  | vlet_bound hbound =>
      cases hbound with
      | externPfn =>
          have hl : TrustedRegistry.lookup? maxCurriedRegistry 10
              = some ⟨builtinMax10Decl, builtinMax10Impl, builtinMax10Spec⟩ := by
            simp [maxCurriedRegistry, TrustedRegistry.lookup?, builtinMax10Decl]
          rw [hl] at hlookup
          cases hlookup
          rfl
      | externPfn_return hret =>
          cases hret with
          | nestedPfn_here =>
              have hl : TrustedRegistry.lookup? maxCurriedRegistry 11
                  = some ⟨builtinMax11CapturesDecl, builtinMax11Impl, builtinMax11CapturesSpec⟩ := by
                simp [maxCurriedRegistry, TrustedRegistry.lookup?,
                  builtinMax10Decl, builtinMax11CapturesDecl]
              rw [hl] at hlookup
              cases hlookup
              rfl
          | nestedPfn_inner hret' => cases hret'
  | vlet_body hbody =>
      -- `(m 7) 2` = `app (app (var m) (num 7)) (num 2)`: no extern declarations.
      cases hbody with
      | app_fun hb1 =>
          cases hb1 with
          | app_fun hb2 => cases hb2
          | app_arg hb2 => cases hb2
      | app_arg hb1 => cases hb1

/-- Per-context trust premise for the applied program at the empty context. -/
private theorem appliedMaxCurried_hagrees :
    TrustedRegistryAgreesWithReachable appliedMaxCurriedProg openEmptyCtx maxCurriedRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) appliedMaxCurried_agreesWithProgram

/-- **Fully-exercised program-level FR for applied curried `max`.** For the program
    `let m = @10 in (m 7) 2`, the trusted registry agrees with the reachable decls,
    so `TypeSystemEnforcesFaultRobustness_at` yields fault-robustness — and because
    the program applies `@11`, the derivation routes that application through
    `builtinMax11CapturesSpec.callFR` (the captured-`a` cleanness gate). -/
theorem appliedMaxCurried_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry maxCurriedRegistry)
      appliedMaxCurriedProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at maxCurriedRegistry appliedMaxCurriedProg s obs openEmptyCtx
    appliedMaxCurried_hagrees

/-- A value that passes the check of a nested pure return is a closure whose
    body is the extern node of the return, which is no pure expression. -/
private theorem validate_nestedPfn {id innerId : ExternId} {innerArg : Name} {innerArgTyp : Typ}
    {innerArgPoison : Bool} {innerArgPred : SyntaxPredicate} {innerRet : ExternReturn}
    {innerCaptures : List Capture} {vRaw v : Value}
    (h : validateExternReturn id (.nestedPfn innerId innerArg innerArgTyp innerArgPoison
      innerArgPred innerRet innerCaptures) vRaw = .ok v) :
    ∃ x body env, v = .peClosure x body env ∧ Expr.toPExpr? body = none := by
  cases vRaw with
  | peClosure y b e =>
      simp only [validateExternReturn] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        have hb := eq_of_beq (show (b == _) = true from hc.2)
        cases h
        exact ⟨y, b, e, rfl, by rw [hb]; rfl⟩
      · cases h
  | _ => simp [validateExternReturn] at h

/-- With `m` the closure of `@10`, a run of `m 7` returns a closure of `@11`,
    whose body is no pure expression. -/
private theorem maxApp_value {c c' : Config} {v : Value} {env : VarEnv}
    (h : terminatesTo (.app (.var "m") (.num 7)) c c' v)
    (hm : c.varEnv.lookup "m" = some (.peClosure "a"
      (.externPfn 10 "a" Typ.int false SyntaxPredicate.noPred builtinMax10RetSpec []) env)) :
    ∃ x body env', v = .peClosure x body env' ∧ Expr.toPExpr? body = none := by
  cases terminatesTo_app_inv_full _ _ _ _ _ h with
  | userFn ht2 ht1 =>
      obtain ⟨rfl, -⟩ := terminatesTo_literal_inv' _ _ rfl _ _ _ ht2
      obtain ⟨v', hl, -, hv⟩ := terminatesTo_var_inv' _ _ _ _ ht1
      rw [hm, Option.some.injEq] at hl
      rw [← hl] at hv; cases hv
  | externFn ht2 ht1 =>
      obtain ⟨rfl, -⟩ := terminatesTo_literal_inv' _ _ rfl _ _ _ ht2
      obtain ⟨v', hl, -, hv⟩ := terminatesTo_var_inv' _ _ _ _ ht1
      rw [hm, Option.some.injEq] at hl
      rw [← hl] at hv; cases hv
  | userPfn ht2 ht1 hne =>
      obtain ⟨rfl, -⟩ := terminatesTo_literal_inv' _ _ rfl _ _ _ ht2
      obtain ⟨v', hl, -, hv⟩ := terminatesTo_var_inv' _ _ _ _ ht1
      rw [hm, Option.some.injEq] at hl
      rw [← hl] at hv
      simp only [Value.peClosure.injEq] at hv
      obtain ⟨-, rfl, -⟩ := hv
      exact absurd Expr.IsExternPfnAst.mk hne
  | externPfn ht2 ht1 _ _ _ hval =>
      obtain ⟨rfl, -⟩ := terminatesTo_literal_inv' _ _ rfl _ _ _ ht2
      obtain ⟨v', hl, -, hv⟩ := terminatesTo_var_inv' _ _ _ _ ht1
      rw [hm, Option.some.injEq] at hl
      rw [← hl] at hv
      simp only [Value.peClosure.injEq, Expr.externPfn.injEq] at hv
      obtain ⟨-, ⟨-, -, -, -, -, hret, -⟩, -⟩ := hv
      rw [hret] at hval
      exact validate_nestedPfn hval

/-- `m` holds the closure of the `@10` declaration. -/
private def MBound (ρ : VarEnv) : Prop :=
  ∃ env, ρ.lookup "m" = some (.peClosure "a"
    (.externPfn 10 "a" Typ.int false SyntaxPredicate.noPred builtinMax10RetSpec []) env)

/-- The steps a run of `appliedMaxCurriedProg` reaches. Both calls apply
    closures of pure externs, whose bodies are no pure expressions, so they
    enter no body. -/
private inductive AppliedMaxStep : Step → Prop
  | prog {s : Step} : s.e = appliedMaxCurriedProg → AppliedMaxStep s
  | decl {s : Step} :
      s.e = .externPfn 10 "a" Typ.int false SyntaxPredicate.noPred builtinMax10RetSpec [] →
      AppliedMaxStep s
  | outer {s : Step} : s.e = .app (.app (.var "m") (.num 7)) (.num 2) →
      MBound s.cfg.varEnv → AppliedMaxStep s
  | inner {s : Step} : s.e = .app (.var "m") (.num 7) → MBound s.cfg.varEnv → AppliedMaxStep s
  | leaf {s : Step} : s.e = .num 7 ∨ s.e = .num 2 ∨ s.e = .var "m" → AppliedMaxStep s

/-- The tests of every run of `appliedMaxCurriedProg` agree with every view:
    the run reaches no conditional. -/
theorem appliedMaxCurried_tests (β : BindVals) (fuel : Nat) (cfg : Config) :
    TestsAgreeWithView β ⟨openEmptyCtx, appliedMaxCurriedProg, fuel, cfg⟩ :=
  testsAgreeWithView_of_closed AppliedMaxStep (.prog rfl)
    (fun {s _} hs h => by
      obtain ⟨_, e, _, c⟩ := s
      cases hs with
      | prog he =>
          obtain rfl : e = _ := he
          unfold appliedMaxCurriedProg at h
          cases h with
          | vletBound => exact .decl rfl
          | vletBody _ hr =>
              refine .outer rfl ⟨c.varEnv, ?_⟩
              rw [terminatesTo_externPfn_value hr]
              simp [VarEnv.update, VarEnv.lookup]
      | decl he => obtain rfl : e = _ := he; cases h
      | outer he hm =>
          obtain rfl : e = _ := he
          obtain ⟨env, hl⟩ := hm
          cases h with
          | appArg => exact .leaf (Or.inr (Or.inl rfl))
          | appFun _ _ => exact .inner rfl ⟨env, hl⟩
          | appFnBody _ _ _ hr1 _ _ =>
              obtain ⟨_, _, _, hv, _⟩ := maxApp_value hr1 hl
              cases hv
          | appPfnBody _ _ _ hr1 _ hpe _ =>
              obtain ⟨_, _, _, hv, hnone⟩ := maxApp_value hr1 hl
              obtain ⟨-, rfl, -⟩ := Value.peClosure.inj hv
              rw [hnone] at hpe
              cases hpe
      | inner he hm =>
          obtain rfl : e = _ := he
          obtain ⟨env, hl⟩ := hm
          cases h with
          | appArg => exact .leaf (Or.inl rfl)
          | appFun _ _ => exact .leaf (Or.inr (Or.inr rfl))
          | appFnBody _ _ _ hr1 _ _ =>
              obtain ⟨v', hl', -, hv⟩ := terminatesTo_var_inv' _ _ _ _ hr1
              have hl'' : c.varEnv.lookup "m" = some v' := hl'
              rw [hl, Option.some.injEq] at hl''
              rw [← hl''] at hv
              cases hv
          | appPfnBody _ _ _ hr1 _ hpe _ =>
              obtain ⟨v', hl', -, hv⟩ := terminatesTo_var_inv' _ _ _ _ hr1
              have hl'' : c.varEnv.lookup "m" = some v' := hl'
              rw [hl, Option.some.injEq] at hl''
              rw [← hl''] at hv
              obtain ⟨-, rfl, -⟩ := Value.peClosure.inj hv
              cases hpe
      | leaf he =>
          rcases he with he | he | he <;> (obtain rfl : e = _ := he; cases h))
    (fun {s _ _ _} hs => by
      cases hs with
      | prog he => rw [he]; intro h; cases h
      | decl he => rw [he]; intro h; cases h
      | outer he _ => rw [he]; intro h; cases h
      | inner he _ => rw [he]; intro h; cases h
      | leaf he => rcases he with he | he | he <;> (rw [he]; intro h; cases h))

end MaxCurriedFR
