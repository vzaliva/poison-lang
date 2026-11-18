/-
  ExternCallSteps.lean — The steps of a typed run and the extern calls made at
  them, with the conditions on each call that the fault-robustness theorem
  takes as premises.  Sits below `StepFR.lean`.
-/

import LeanProofs.RegimeConsistency
import Mathlib.Logic.Relation

/-!
# Extern calls along a typed run

The fault-robustness theorem treats the outputs of extern calls as inputs: a
value returned by an extern call is checked against the predicate of the tag
the call allocates, and its agreement in two runs is assumed where that tag is
true. This module defines the places where these assumptions are made.

* A `Step` is a typing context, an expression, the fuel of its typing and the
  start configuration of its run.
* `SubStep s s'` holds when the proof of the step theorem at `s` recurses into
  `s'`: `s'` is a part of `s.e`, typed in the context the typechecker uses for
  it and run from the configuration the interpreter uses for it. Side
  conditions fix the typing results and the runs of the parts that come
  before. `Reach root` is the reflexive and transitive closure.
* `ExternCallAt s effects entry res cf o` holds when the step `s` is an
  application whose run calls an extern: `res` is the typing result of the
  member of the function type that the call is typed against, `entry` is the
  call entry, `cf` and `o` are the final configuration and the returned value.
* `CallMatches` and `CallAgrees` are the conditions on one call: the predicate
  of a tag the call allocated holds on the returned value exactly when the
  regime after the call says true; and where such a tag is true, the returned
  value is the same in two runs. The same conditions apply to the cells the
  call writes through its effects (`EffectCell`).
* `ExternValAt s res cf o` holds when the step `s` declares an `extern val`;
  `ValMatches` is the condition *match* on the declared value. An
  `extern val` is read as a constant extern function: its guard tag is
  fresh, and its value comes from outside the program. *Match* for a
  declaration is a premise, handed to the declaration contracts. Agreement
  of the declared value in two runs is not a premise: the author of the
  entry proves it in the entry's declaration contract.

Nothing here is stored at run time: the typing of a step is recomputed by the
typechecker from the step.

One runtime call can be typed against several members of a function type (two
members with the same extern code). The conditions are then asked for each
member.
-/

open Std LeanPoison

/-! ## Steps -/

/-- A typing context, an expression, the fuel of the typing and the start
    configuration of the run. -/
structure Step where
  ctx  : TypeContext
  e    : Expr
  fuel : Nat
  cfg  : Config

/-- `applyClosuresThreaded applyOne items cursor bn` applies the member `x` at the
    cursor `cursor'` and binding number `bn'` with result `r`: the members are
    applied in order, each at the cursor and binding number the previous one
    left. -/
inductive ThreadedAt {α : Type} (applyOne : α → Tag × Loc → Nat → TypecheckM TypeResult) :
    List α → Tag × Loc → Nat → α → Tag × Loc → Nat → TypeResult → Prop where
  | here {item : α} {rest : List α} {cursor : Tag × Loc} {bn : Nat} {r : TypeResult} :
      applyOne item cursor bn = .ok r →
      ThreadedAt applyOne (item :: rest) cursor bn item cursor bn r
  | there {item x : α} {rest : List α} {cursor cursor' : Tag × Loc} {bn bn' : Nat}
      {r rx : TypeResult} :
      applyOne item cursor bn = .ok r →
      ThreadedAt applyOne rest (r.nextTag', r.nextLoc') r.nextBind' x cursor' bn' rx →
      ThreadedAt applyOne (item :: rest) cursor bn x cursor' bn' rx

/-- The member application of `typecheckApp` for an impure arrow: `r2` types
    the argument, `r1` the function. -/
def fnApply (ctx : TypeContext) (r2 r1 : TypeResult) (st1 st2 : Typ) (p : Poison) (G : Nat) :
    FnTClosure → Tag × Loc → Nat → TypecheckM TypeResult :=
  fun tcl cursor bn => applyFnTClosureAtCursor tcl st1 st2 p r1.qualType.poison
    r2.qualType.etyp r2.qualType.poison r2.qualType.pred ctx r1 cursor bn G

/-- The member application of `typecheckApp` for a pure arrow. -/
def pfnApply (ctx : TypeContext) (r2 r1 : TypeResult) (st1 st2 : Typ) (p : Poison) (G : Nat) :
    PFnTClosure → Tag × Loc → Nat → TypecheckM TypeResult :=
  fun tcl cursor bn => applyPFnTClosureAtCursor tcl st1 st2 p r1.qualType.poison
    r2.qualType.etyp r2.qualType.poison r2.qualType.pred ctx r1 cursor bn G

/-- The body context of an impure member (`applyFnTClosureAtCursor`,
    `ExternBoundaryTyping.Call.fnExternMember`). -/
def fnBodyCtx (ctx : TypeContext) (r2 r1 : TypeResult) (p : Poison) (x : Name)
    (tenv : CapturedVarEnv) (cursor : Tag × Loc) (bn : Nat) : TypeContext :=
  { ctx with
    pc := joinPoison p (joinPoison r1.qualType.poison ctx.pc)
    memEnv := r1.memEnv'
    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
      ⟨r2.qualType.etyp, joinPoison ctx.pc r2.qualType.poison, r2.qualType.pred⟩
    bindEnv := BindEnv.bindParam tenv x bn
    tagEnv := r1.tagEnv'
    nextTag := cursor.1
    nextBind := bn + 1
    nextLoc := cursor.2
    regime := r1.regime'
    externRefAllowed := false
    declaredExternRefs := r1.declared' }

/-- The body context of a pure member (`applyPFnTClosureAtCursor`,
    `ExternBoundaryTyping.Call.pfnExternMember`). -/
def pfnBodyCtx (ctx : TypeContext) (r2 r1 : TypeResult) (p : Poison) (x : Name)
    (tenv : CapturedVarEnv) (cursor : Tag × Loc) (bn : Nat) : TypeContext :=
  { ctx with
    pc := joinPoison p (joinPoison ctx.pc r1.qualType.poison)
    memEnv := r1.memEnv'
    varEnv := VarTypeEnv.update (VarTypeEnv.ofCaptured tenv) x
      ⟨r2.qualType.etyp, joinPoison ctx.pc r2.qualType.poison, r2.qualType.pred⟩
    bindEnv := BindEnv.bindParam tenv x bn
    tagEnv := r1.tagEnv'
    pureCtx := true
    nextTag := cursor.1
    nextBind := bn + 1
    nextLoc := cursor.2
    regime := r1.regime'
    externRefAllowed := false
    declaredExternRefs := r1.declared' }

/-- The branch contexts of a conditional whose guard matches a tag `k` with an
    entry in the regime (`typecheckIf`). `r1` types the condition in pure mode,
    `r2` the then-branch; the else-branch is typed after both. -/
def ctxTrue (ctx : TypeContext) (k : Tag) (deps : Deps) (r1 : TypeResult) : TypeContext :=
  { ctx with tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
             nextTag := r1.nextTag', nextBind := r1.nextBind',
             declaredExternRefs := r1.declared' }

/-- See `ctxTrue`. -/
def ctxFalse' (ctx : TypeContext) (k : Tag) (deps : Deps) (r2 : TypeResult) : TypeContext :=
  { ctx with tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
             nextTag := r2.nextTag', nextLoc := r2.nextLoc', nextBind := r2.nextBind',
             declaredExternRefs := r2.declared' }

/-- The then-branch context of a conditional typed by the standard rule; `r1`
    types the condition. -/
def ctxStd (ctx : TypeContext) (r1 : TypeResult) : TypeContext :=
  { ctxAfter ctx r1 with pc := joinPoison ctx.pc r1.qualType.poison }

/-- The else-branch context of a conditional typed by the standard rule; `r2`
    types the then-branch. -/
def ctxStdElse (ctx : TypeContext) (r1 r2 : TypeResult) : TypeContext :=
  { ctxStd ctx r1 with nextLoc := r2.nextLoc', nextTag := r2.nextTag', nextBind := r2.nextBind',
                       declaredExternRefs := r2.declared' }

/-- `typecheckIf` uses the standard rule: no guard matches the condition, or the
    matched tag has no entry in the regime. -/
def StdArm (ctx : TypeContext) (e1 : Expr) (f : Nat) : Prop :=
  (∃ msg, matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .error msg) ∨
  (∃ k deps, matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .ok (k, deps) ∧ ctx.regime.lookup? k = none)

/-- The parts of a step. A composite expression typed at fuel `f + 2` has its
    parts typed at fuel `f` (`typecheckExpr` and the rule each use one unit). -/
inductive SubStep : Step → Step → Prop where
  -- Binary operator: left part, then right part after it.
  | opLeft {ctx : TypeContext} {e1 e2 : Expr} {o : Op} {f : Nat} {cfg : Config} :
      SubStep ⟨ctx, .op e1 o e2, f + 2, cfg⟩ ⟨ctx, e1, f, cfg⟩
  | opRight {ctx : TypeContext} {e1 e2 : Expr} {o : Op} {f : Nat} {cfg : Config}
      {r1 : TypeResult} {c1 : Config} {v1 : Value} :
      typecheckExpr ctx e1 f = .ok r1 →
      terminatesTo e1 cfg c1 v1 →
      SubStep ⟨ctx, .op e1 o e2, f + 2, cfg⟩ ⟨ctxAfter ctx r1, e2, f, c1⟩
  -- Unary operator, reference allocation, dereference.
  | unary {ctx : TypeContext} {e : Expr} {o : UnaryOp} {f : Nat} {cfg : Config} :
      SubStep ⟨ctx, .unaryop o e, f + 2, cfg⟩ ⟨ctx, e, f, cfg⟩
  | newRef {ctx : TypeContext} {e : Expr} {f : Nat} {cfg : Config} :
      SubStep ⟨ctx, .newRef e, f + 2, cfg⟩ ⟨ctx, e, f, cfg⟩
  | deref {ctx : TypeContext} {e : Expr} {f : Nat} {cfg : Config} :
      SubStep ⟨ctx, .deref e, f + 2, cfg⟩ ⟨ctx, e, f, cfg⟩
  -- Assignment: target, then value.
  | assignLeft {ctx : TypeContext} {e1 e2 : Expr} {f : Nat} {cfg : Config} :
      SubStep ⟨ctx, .assign e1 e2, f + 2, cfg⟩ ⟨ctx, e1, f, cfg⟩
  | assignRight {ctx : TypeContext} {e1 e2 : Expr} {f : Nat} {cfg : Config}
      {r1 : TypeResult} {c1 : Config} {v1 : Value} :
      typecheckExpr ctx e1 f = .ok r1 →
      terminatesTo e1 cfg c1 v1 →
      SubStep ⟨ctx, .assign e1 e2, f + 2, cfg⟩ ⟨ctxAfter ctx r1, e2, f, c1⟩
  -- Sequence.
  | seqLeft {ctx : TypeContext} {e1 e2 : Expr} {f : Nat} {cfg : Config} :
      SubStep ⟨ctx, .seq e1 e2, f + 2, cfg⟩ ⟨ctx, e1, f, cfg⟩
  | seqRight {ctx : TypeContext} {e1 e2 : Expr} {f : Nat} {cfg : Config}
      {r1 : TypeResult} {c1 : Config} {v1 : Value} :
      typecheckExpr ctx e1 f = .ok r1 →
      terminatesTo e1 cfg c1 v1 →
      SubStep ⟨ctx, .seq e1 e2, f + 2, cfg⟩ ⟨ctxAfter ctx r1, e2, f, c1⟩
  -- Let binding: bound expression, then body.
  | vletBound {ctx : TypeContext} {x : Name} {e1 e2 : Expr} {f : Nat} {cfg : Config} :
      SubStep ⟨ctx, .vlet x e1 e2, f + 2, cfg⟩ ⟨ctx, e1, f, cfg⟩
  | vletBody {ctx : TypeContext} {x : Name} {e1 e2 : Expr} {f : Nat} {cfg : Config}
      {r1 : TypeResult} {c1 : Config} {v1 : Value} :
      typecheckExpr ctx e1 f = .ok r1 →
      terminatesTo e1 cfg c1 v1 →
      SubStep ⟨ctx, .vlet x e1 e2, f + 2, cfg⟩
        ⟨{ ctxAfter ctx r1 with varEnv := ctx.varEnv.update x r1.qualType,
                                bindEnv := ctx.bindEnv.insert x r1.nextBind',
                                nextBind := r1.nextBind' + 1 }, e2, f,
         { c1 with varEnv := cfg.varEnv.update x v1 }⟩
  -- Conditional whose guard matches a tag with an entry in the regime: the
  -- condition in pure mode, then the branch the run takes.
  | iteCondPure {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config}
      {k : Tag} {deps : Deps} {b : Bool} :
      matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .ok (k, deps) →
      ctx.regime.lookup? k = some b →
      SubStep ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ ⟨{ ctx with pureCtx := true }, e1, f, cfg⟩
  | iteThenMatched {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config}
      {k : Tag} {deps : Deps} {b : Bool} {r1 : TypeResult} {c1 : Config} :
      matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .ok (k, deps) →
      ctx.regime.lookup? k = some b →
      typecheckExpr { ctx with pureCtx := true } e1 f = .ok r1 →
      terminatesTo e1 cfg c1 (.bool true) →
      SubStep ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ ⟨ctxTrue ctx k deps r1, e2, f, c1⟩
  | iteElseMatched {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config}
      {k : Tag} {deps : Deps} {b : Bool} {r1 r2 : TypeResult} {c1 : Config} :
      matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .ok (k, deps) →
      ctx.regime.lookup? k = some b →
      typecheckExpr { ctx with pureCtx := true } e1 f = .ok r1 →
      terminatesTo e1 cfg c1 (.bool false) →
      typecheckExpr (ctxTrue ctx k deps r1) e2 f = .ok r2 →
      SubStep ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ ⟨ctxFalse' ctx k deps r2, e3, f, c1⟩
  -- Conditional typed by the standard rule.
  | iteCondStd {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config} :
      StdArm ctx e1 f →
      SubStep ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ ⟨ctx, e1, f, cfg⟩
  | iteThenStd {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config}
      {r1 : TypeResult} {c1 : Config} :
      StdArm ctx e1 f →
      typecheckExpr ctx e1 f = .ok r1 →
      terminatesTo e1 cfg c1 (.bool true) →
      SubStep ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ ⟨ctxStd ctx r1, e2, f, c1⟩
  | iteElseStd {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config}
      {r1 r2 : TypeResult} {c1 : Config} :
      StdArm ctx e1 f →
      typecheckExpr ctx e1 f = .ok r1 →
      terminatesTo e1 cfg c1 (.bool false) →
      typecheckExpr (ctxStd ctx r1) e2 f = .ok r2 →
      SubStep ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ ⟨ctxStdElse ctx r1 r2, e3, f, c1⟩
  -- Application: argument, function, then the body of the member the run
  -- calls, at the cursor `applyClosuresThreaded` gives that member, whose
  -- captured types type the closure's environment.
  | appArg {ctx : TypeContext} {e1 e2 : Expr} {G : Nat} {cfg : Config} :
      SubStep ⟨ctx, .app e1 e2, G + 2, cfg⟩ ⟨ctx, e2, G, cfg⟩
  | appFun {ctx : TypeContext} {e1 e2 : Expr} {G : Nat} {cfg : Config}
      {r2 : TypeResult} {c2 : Config} {v2 : Value} :
      typecheckExpr ctx e2 G = .ok r2 →
      terminatesTo e2 cfg c2 v2 →
      SubStep ⟨ctx, .app e1 e2, G + 2, cfg⟩
        ⟨ctxAfter ctx r2, e1, G, { c2 with varEnv := cfg.varEnv }⟩
  | appFnBody {ctx : TypeContext} {e1 e2 : Expr} {H : Nat} {cfg : Config}
      {r2 r1 rb : TypeResult} {c2 c1 : Config} {v2 : Value}
      {x : Name} {body : Expr} {env : VarEnv}
      {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
      {tenv : CapturedVarEnv} {cursor : Tag × Loc} {bn : Nat} :
      typecheckExpr ctx e2 (H + 1) = .ok r2 →
      terminatesTo e2 cfg c2 v2 →
      typecheckExpr (ctxAfter ctx r2) e1 (H + 1) = .ok r1 →
      terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1 (.closure x body env) →
      r1.qualType.etyp = .arrow st1 st2 p tcls →
      ThreadedAt (fnApply ctx r2 r1 st1 st2 p (H + 1)) tcls (r1.nextTag', r1.nextLoc')
        r1.nextBind' (.regular x body tenv) cursor bn rb →
      (∃ θ, capturedVarsTypingProperty θ tenv env) →
      SubStep ⟨ctx, .app e1 e2, H + 3, cfg⟩
        ⟨fnBodyCtx ctx r2 r1 p x tenv cursor bn, body, H,
         { c1 with varEnv := env.update x v2, pureMode := false }⟩
  | appPfnBody {ctx : TypeContext} {e1 e2 : Expr} {H : Nat} {cfg : Config}
      {r2 r1 rb : TypeResult} {c2 c1 : Config} {v2 : Value}
      {x : Name} {body : Expr} {pbody : PExpr} {env : VarEnv}
      {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
      {tenv : CapturedVarEnv} {cursor : Tag × Loc} {bn : Nat} :
      typecheckExpr ctx e2 (H + 1) = .ok r2 →
      terminatesTo e2 cfg c2 v2 →
      typecheckExpr (ctxAfter ctx r2) e1 (H + 1) = .ok r1 →
      terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1 (.peClosure x body env) →
      r1.qualType.etyp = .parrow st1 st2 p tcls →
      Expr.toPExpr? body = some pbody →
      ThreadedAt (pfnApply ctx r2 r1 st1 st2 p (H + 1)) tcls (r1.nextTag', r1.nextLoc')
        r1.nextBind' (.regular x pbody tenv) cursor bn rb →
      (∃ θ, capturedVarsTypingProperty θ tenv env) →
      SubStep ⟨ctx, .app e1 e2, H + 3, cfg⟩
        ⟨pfnBodyCtx ctx r2 r1 p x tenv cursor bn, PExpr.toExpr pbody, H,
         { c1 with varEnv := env.update x v2, pureMode := true }⟩

/-- The steps reachable from a root. -/
def Reach (root : Step) : Step → Prop := Relation.ReflTransGen SubStep root

/-! ## Extern calls -/

/-- An application step whose run calls an extern. `effects` are the declared
    effects of the extern (none for a pure extern), `res` is the typing result
    of the member of the function type the call is typed against, `entry` is
    the call entry, and `cf`, `o` are the final configuration and the returned
    value of the call. -/
inductive ExternCallAt :
    Step → List Effect → ExternCallEntry → TypeResult → Config → Value → Prop where
  | pfn {ctx : TypeContext} {e1 e2 : Expr} {G : Nat} {cfg : Config}
      {r2 r1 res : TypeResult} {c2 c1 : Config} {v2 vRaw o : Value}
      {x y : Name} {env : VarEnv} {id : ExternId} {argTyp : Typ} {argPoison : Bool}
      {argPred : SyntaxPredicate} {retSpec : ExternReturn} {captures memberCaptures : List Capture}
      {st1 st2 : Typ} {p : Poison} {tcls : List PFnTClosure}
      {tenv : CapturedVarEnv} {declaredArgQt : QTyp} {cursor : Tag × Loc} {bn : Nat}
      {implFn : VarEnv → Value → Memory → Except ExternError Value} :
      typecheckExpr ctx e2 G = .ok r2 →
      terminatesTo e2 cfg c2 v2 →
      typecheckExpr (ctxAfter ctx r2) e1 G = .ok r1 →
      terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1
        (.peClosure x (.externPfn id y argTyp argPoison argPred retSpec captures) env) →
      r1.qualType.etyp = .parrow st1 st2 p tcls →
      ThreadedAt (pfnApply ctx r2 r1 st1 st2 p G) tcls (r1.nextTag', r1.nextLoc')
        r1.nextBind' (.extern id x retSpec tenv declaredArgQt memberCaptures) cursor bn res →
      c1.registry.get? id = some (.pfn implFn) →
      valueMatchesTyp v2 argTyp = true →
      implFn (env.update x v2) v2 c1.memory = .ok vRaw →
      validateExternReturn id retSpec vRaw = .ok o →
      ExternCallAt ⟨ctx, .app e1 e2, G + 2, cfg⟩ []
        (ExternCallEntry.ofRuntime (pfnBodyCtx ctx r2 r1 p x tenv cursor bn) c1 env x v2)
        res c1 o
  | fn {ctx : TypeContext} {e1 e2 : Expr} {G : Nat} {cfg : Config}
      {r2 r1 res : TypeResult} {c2 c1 : Config} {v2 vRaw o : Value}
      {x y : Name} {env : VarEnv} {id : ExternId} {argTyp : Typ} {argPoison : Bool}
      {argPred : SyntaxPredicate} {retSpec : ExternReturn} {effects : List Effect}
      {captures memberCaptures : List Capture}
      {st1 st2 : Typ} {p : Poison} {tcls : List FnTClosure}
      {tenv : CapturedVarEnv} {declaredArgQt : QTyp} {cursor : Tag × Loc} {bn : Nat}
      {implFn : VarEnv → Value → Memory → Address →
        Except ExternError (Value × Memory × Address)}
      {mem' : Memory} {addr' : Address} :
      typecheckExpr ctx e2 G = .ok r2 →
      terminatesTo e2 cfg c2 v2 →
      typecheckExpr (ctxAfter ctx r2) e1 G = .ok r1 →
      terminatesTo e1 { c2 with varEnv := cfg.varEnv } c1
        (.closure x (.externFn id y argTyp argPoison argPred retSpec effects captures) env) →
      r1.qualType.etyp = .arrow st1 st2 p tcls →
      ThreadedAt (fnApply ctx r2 r1 st1 st2 p G) tcls (r1.nextTag', r1.nextLoc')
        r1.nextBind' (.extern id x retSpec effects tenv declaredArgQt memberCaptures) cursor bn res →
      c1.pureMode = false →
      c1.registry.get? id = some (.fn implFn) →
      valueMatchesTyp v2 argTyp = true →
      implFn (env.update x v2) v2 c1.memory c1.nextAddr = .ok (vRaw, mem', addr') →
      validateExternReturn id retSpec vRaw = .ok o →
      ExternCallAt ⟨ctx, .app e1 e2, G + 2, cfg⟩ effects
        (ExternCallEntry.ofRuntime (fnBodyCtx ctx r2 r1 p x tenv cursor bn) c1 env x v2)
        res { c1 with memory := mem', nextAddr := addr' } o

/-! ## The conditions on one call -/

/-- `EffectCell entry effects res v addr qt`: an effect `!v` of the call writes
    the cell at `addr`, and `qt` is the type the typing of the call stored for
    it. In the body context, `v` is a reference to the single location `l`; at
    run time it holds the address `addr`; `qt` is the entry for `l` in the
    member result. A target whose type names several locations is updated
    weakly and gives no cell here. -/
inductive EffectCell (entry : ExternCallEntry) (effects : List Effect) (res : TypeResult) :
    Name → Address → QTyp → Prop where
  | mk {ef : Effect} {v : Name} {qtv : QTyp} {ls : LocSet} {l : Loc} {addr : Address}
      {qt : QTyp} :
      ef ∈ effects → ef.target = .namedVar v →
      entry.bodyCtx.varEnv.lookup v = some qtv → qtv.etyp = .ref ls → ls.toList = [l] →
      res.memEnv'.lookup l = some qt →
      entry.unifiedEnv.lookup v = some (.loc addr) →
      EffectCell entry effects res v addr qt

/-- A call without effects writes no cell. -/
theorem EffectCell.not_nil {entry : ExternCallEntry} {res : TypeResult} {v : Name}
    {addr : Address} {qt : QTyp} : ¬ EffectCell entry [] res v addr qt := by
  rintro ⟨hef, _, _, _, _, _, _⟩
  cases hef

/-- *Match* for one call: for each tag the call allocated that carries a
    predicate on the returned value or on a cell the call writes, the predicate
    holds exactly when the regime after the call says true. This is what the
    constructors `inRegimeTrue` and `inRegimeFalse` of
    `valueConsistentWithRegime` ask of the value, and the constructor
    `withPred_ok` of `locsRegime` asks of the cell; a guard without predicate
    asks nothing. -/
structure CallMatches (predSat : PredSat) (entry : ExternCallEntry) (effects : List Effect)
    (res : TypeResult) (cf : Config) (o : Value) : Prop where
  ret : ∀ a ∈ res.tagLog', ∀ (argName : Name) (body : PExpr) (cap : CapturedVarEnv) (b : Bool),
    res.qualType.pred = .guardClosure a.tag argName body cap →
    res.regime'.lookup? a.tag = some b →
    (predSat a.tag cf.memory o ↔ b = true)
  cells : ∀ (v : Name) (addr : Address) (qt : QTyp) (n : Int),
    EffectCell entry effects res v addr qt → cf.memory.lookup addr = some n →
    ∀ a ∈ res.tagLog', ∀ (argName : Name) (body : PExpr) (cap : CapturedVarEnv) (b : Bool),
    qt.pred = .guardClosure a.tag argName body cap →
    res.regime'.lookup? a.tag = some b →
    (predSat a.tag cf.memory (.num n) ↔ b = true)

/-- *Agreement* for one call made by both runs: where a tag the call allocated
    is true, a returned value that is not a function or a reference is the
    same in both runs, and so is the content of each cell that an effect `!v`
    writes and whose stored type carries that tag. This is what the
    constructor `withPred_true_eq` of `agreeValueUnder` asks of the two
    values. -/
structure CallAgrees (entry₀ entry₁ : ExternCallEntry) (effects : List Effect) (res : TypeResult)
    (cf₀ cf₁ : Config) (o₀ o₁ : Value) : Prop where
  ret : ∀ a ∈ res.tagLog',
    qtypGuardTag res.qualType = some a.tag →
    res.regime'.lookup? a.tag = some true →
    res.qualType.etyp.isFunctionType = false →
    (¬ ∃ ls, res.qualType.etyp = ETyp.ref ls) →
    o₀ = o₁
  cells : ∀ (v : Name) (addr₀ addr₁ : Address) (qt : QTyp) (n₀ n₁ : Int),
    EffectCell entry₀ effects res v addr₀ qt → EffectCell entry₁ effects res v addr₁ qt →
    cf₀.memory.lookup addr₀ = some n₀ → cf₁.memory.lookup addr₁ = some n₁ →
    ∀ a ∈ res.tagLog', qtypGuardTag qt = some a.tag →
    res.regime'.lookup? a.tag = some true →
    n₀ = n₁

/-- `ExternValAt s res cf o`: the step `s` declares an `extern val`, typed
    with the result `res`; the run returns `o` and ends in `cf`. -/
inductive ExternValAt : Step → TypeResult → Config → Value → Prop where
  | mk {ctx : TypeContext} {id : ExternId} {typ : Typ} {poison : Bool}
      {pred : SyntaxPredicate} {G : Nat} {cfg cf : Config} {res : TypeResult} {o : Value} :
      typecheckExpr ctx (.externVal id typ poison pred) G = .ok res →
      terminatesTo (.externVal id typ poison pred) cfg cf o →
      ExternValAt ⟨ctx, .externVal id typ poison pred, G, cfg⟩ res cf o

/-- *Match* for one `extern val`: for each tag the declaration allocated that
    carries a predicate on the declared value, the predicate holds exactly
    when the regime after the declaration says true. -/
def ValMatches (predSat : PredSat) (res : TypeResult) (cf : Config) (o : Value) : Prop :=
  ∀ a ∈ res.tagLog', ∀ (argName : Name) (body : PExpr) (cap : CapturedVarEnv) (b : Bool),
    res.qualType.pred = .guardClosure a.tag argName body cap →
    res.regime'.lookup? a.tag = some b →
    (predSat a.tag cf.memory o ↔ b = true)

/-! ## The premises on runs -/

/-- Every extern call and every `extern val` declaration of the run from
    `root` satisfies *match*. -/
structure ExternCallsMatch (predSat : PredSat) (root : Step) : Prop where
  calls : ∀ s effects entry res cf o, Reach root s → ExternCallAt s effects entry res cf o →
    CallMatches predSat entry effects res cf o
  vals : ∀ s res cf o, Reach root s → ExternValAt s res cf o → ValMatches predSat res cf o

/-- Every extern call that both runs make satisfies *agreement*. Two calls are
    the same call when they are made at the same typing step (context,
    expression and fuel), are typed against the same member result and have
    the same body context. The `extern val` declarations have no premise
    here: agreement of a declared value is proved for each entry. -/
structure ExternCallsAgree (root₀ root₁ : Step) : Prop where
  calls : ∀ s₀ s₁ effects entry₀ entry₁ res cf₀ cf₁ o₀ o₁,
    Reach root₀ s₀ → Reach root₁ s₁ →
    s₀.ctx = s₁.ctx → s₀.e = s₁.e → s₀.fuel = s₁.fuel →
    ExternCallAt s₀ effects entry₀ res cf₀ o₀ → ExternCallAt s₁ effects entry₁ res cf₁ o₁ →
    entry₀.bodyCtx = entry₁.bodyCtx →
    CallAgrees entry₀ entry₁ effects res cf₀ cf₁ o₀ o₁

/-! ## Guard variables at matched conditionals -/

/-- The variables the guards of a matched conditional read hold the values the
    view `β` gives their binding numbers: at every step reachable from `root`
    that is a conditional whose condition `matchGuard` matches to a tag `k` with
    an entry in the regime, every guard with tag `k` in the context reads, other
    than its argument, only variables whose values in the run's environment are
    the values `β` gives their binding numbers (`ViewAgreesOn`). -/
structure TestsAgreeWithView (β : BindVals) (root : Step) : Prop where
  tests : ∀ {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config}
      {k : Tag} {deps : Deps} {b : Bool} {d : GuardDesc},
    Reach root ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ →
    matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .ok (k, deps) →
    ctx.regime.lookup? k = some b →
    GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k d →
    ViewAgreesOn β ctx.bindEnv cfg.varEnv (PExpr.freeVars [d.argName] d.body)

/-- `TestsAgreeWithView` on a set of steps closed under `SubStep`, the form the
    step lemmas carry. -/
structure TestsAgreeWithViewOn (β : BindVals) (P : Step → Prop) : Prop where
  closed : ∀ {s s' : Step}, P s → SubStep s s' → P s'
  tests : ∀ {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat} {cfg : Config}
      {k : Tag} {deps : Deps} {b : Bool} {d : GuardDesc},
    P ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩ →
    matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .ok (k, deps) →
    ctx.regime.lookup? k = some b →
    GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k d →
    ViewAgreesOn β ctx.bindEnv cfg.varEnv (PExpr.freeVars [d.argName] d.body)

theorem TestsAgreeWithViewOn.of_root {β : BindVals} {root : Step}
    (h : TestsAgreeWithView β root) : TestsAgreeWithViewOn β (Reach root) where
  closed hs hstep := Relation.ReflTransGen.tail hs hstep
  tests hs hm hk hd := h.tests hs hm hk hd

/-- The hypothesis of `PredSatLaws.match_iff` at a matched conditional of the set. -/
theorem TestsAgreeWithViewOn.at_ite {β : BindVals} {P : Step → Prop}
    (h : TestsAgreeWithViewOn β P) {ctx : TypeContext} {e1 e2 e3 : Expr} {f : Nat}
    {cfg : Config} {k : Tag} {deps : Deps} {b : Bool}
    (hs : P ⟨ctx, .ite e1 e2 e3, f + 2, cfg⟩)
    (hm : matchGuard e1 ctx.memEnv ctx.varEnv ctx.bindEnv f = .ok (k, deps))
    (hk : ctx.regime.lookup? k = some b) :
    ∀ d, GuardDescInEnvsDeep ctx.varEnv ctx.memEnv k d →
      ViewAgreesOn β ctx.bindEnv cfg.varEnv (PExpr.freeVars [d.argName] d.body) :=
  fun _ hd => h.tests hs hm hk hd

/-! ## The form carried by the step proof

The step proof works with sets of steps closed under `SubStep` rather than
with a root: a set of steps of one run whose extern calls satisfy *match*, and
for two runs, *agreement* between the calls of the two sets. -/

/-- A set of steps of one run that is closed under `SubStep` and whose extern
    calls and `extern val` declarations satisfy *match*. -/
structure ExternCallsMatchOn (predSat : PredSat) (P : Step → Prop) : Prop where
  closed : ∀ {s s' : Step}, P s → SubStep s s' → P s'
  calls : ∀ {s : Step} {effects : List Effect} {entry : ExternCallEntry} {res : TypeResult}
    {cf : Config} {o : Value},
    P s → ExternCallAt s effects entry res cf o → CallMatches predSat entry effects res cf o
  vals : ∀ {s : Step} {res : TypeResult} {cf : Config} {o : Value},
    P s → ExternValAt s res cf o → ValMatches predSat res cf o

/-- The extern calls of two sets of steps that are the same call satisfy
    *agreement* (see `ExternCallsAgree`). -/
def ExternCallsAgreeOn (P₀ P₁ : Step → Prop) : Prop :=
  ∀ {s₀ s₁ : Step} {effects : List Effect} {entry₀ entry₁ : ExternCallEntry} {res : TypeResult}
    {cf₀ cf₁ : Config} {o₀ o₁ : Value},
    P₀ s₀ → P₁ s₁ →
    s₀.ctx = s₁.ctx → s₀.e = s₁.e → s₀.fuel = s₁.fuel →
    ExternCallAt s₀ effects entry₀ res cf₀ o₀ → ExternCallAt s₁ effects entry₁ res cf₁ o₁ →
    entry₀.bodyCtx = entry₁.bodyCtx →
    CallAgrees entry₀ entry₁ effects res cf₀ cf₁ o₀ o₁

/-- The premises on extern calls for two runs, carried by the step theorem.
    Each run has its own relation and its own view of the values of binding
    numbers; `tests₀` and `tests₁` state, for each run, that the guards of its
    matched conditionals read variables holding the values of that run's view. -/
structure ExternStepPremises (predSat₀ predSat₁ : PredSat) (β₀ β₁ : BindVals)
    (P₀ P₁ : Step → Prop) : Prop where
  run₀ : ExternCallsMatchOn predSat₀ P₀
  run₁ : ExternCallsMatchOn predSat₁ P₁
  agree : ExternCallsAgreeOn P₀ P₁
  tests₀ : TestsAgreeWithViewOn β₀ P₀
  tests₁ : TestsAgreeWithViewOn β₁ P₁

theorem ExternCallsMatchOn.of_root {predSat : PredSat} {root : Step}
    (h : ExternCallsMatch predSat root) : ExternCallsMatchOn predSat (Reach root) where
  closed hs hstep := Relation.ReflTransGen.tail hs hstep
  calls hs hcall := h.calls _ _ _ _ _ _ hs hcall
  vals hs hval := h.vals _ _ _ _ hs hval

theorem ExternCallsAgreeOn.of_roots {root₀ root₁ : Step}
    (h : ExternCallsAgree root₀ root₁) : ExternCallsAgreeOn (Reach root₀) (Reach root₁) :=
  fun hs₀ hs₁ hctx he hfuel hcall₀ hcall₁ hbody =>
    h.calls _ _ _ _ _ _ _ _ _ _ hs₀ hs₁ hctx he hfuel hcall₀ hcall₁ hbody

theorem ExternStepPremises.of_roots {predSat₀ predSat₁ : PredSat} {β₀ β₁ : BindVals}
    {root₀ root₁ : Step}
    (h₀ : ExternCallsMatch predSat₀ root₀) (h₁ : ExternCallsMatch predSat₁ root₁)
    (hagree : ExternCallsAgree root₀ root₁)
    (ht₀ : TestsAgreeWithView β₀ root₀) (ht₁ : TestsAgreeWithView β₁ root₁) :
    ExternStepPremises predSat₀ predSat₁ β₀ β₁ (Reach root₀) (Reach root₁) :=
  ⟨.of_root h₀, .of_root h₁, ExternCallsAgreeOn.of_roots hagree,
    .of_root ht₀, .of_root ht₁⟩

theorem Reach.refl (root : Step) : Reach root root := Relation.ReflTransGen.refl

/-- A program without extern calls and `extern val` declarations meets the
    premises for any two runs. -/
theorem ExternStepPremises.of_noCalls {predSat₀ predSat₁ : PredSat} {β₀ β₁ : BindVals}
    {P₀ P₁ : Step → Prop}
    (hclosed₀ : ∀ {s s' : Step}, P₀ s → SubStep s s' → P₀ s')
    (hclosed₁ : ∀ {s s' : Step}, P₁ s → SubStep s s' → P₁ s')
    (hnone₀ : ∀ {s effects entry res cf o}, P₀ s → ¬ ExternCallAt s effects entry res cf o)
    (hnone₁ : ∀ {s effects entry res cf o}, P₁ s → ¬ ExternCallAt s effects entry res cf o)
    (hnoval₀ : ∀ {s res cf o}, P₀ s → ¬ ExternValAt s res cf o)
    (hnoval₁ : ∀ {s res cf o}, P₁ s → ¬ ExternValAt s res cf o)
    (ht₀ : TestsAgreeWithViewOn β₀ P₀) (ht₁ : TestsAgreeWithViewOn β₁ P₁) :
    ExternStepPremises predSat₀ predSat₁ β₀ β₁ P₀ P₁ :=
  ⟨⟨hclosed₀, fun hs hcall => (hnone₀ hs hcall).elim, fun hs hval => (hnoval₀ hs hval).elim⟩,
   ⟨hclosed₁, fun hs hcall => (hnone₁ hs hcall).elim, fun hs hval => (hnoval₁ hs hval).elim⟩,
   fun hs₀ _ _ _ _ hcall₀ _ _ => (hnone₀ hs₀ hcall₀).elim, ht₀, ht₁⟩

/-! ## Runs without extern entries -/

/-- A step and its parts run under the same registry. -/
theorem SubStep.registry_eq {s s' : Step} (h : SubStep s s') :
    s'.cfg.registry = s.cfg.registry := by
  cases h with
  | opRight _ ht => have h := terminatesTo_preserves_registry ht; exact h
  | assignRight _ ht => have h := terminatesTo_preserves_registry ht; exact h
  | seqRight _ ht => have h := terminatesTo_preserves_registry ht; exact h
  | vletBody _ ht => have h := terminatesTo_preserves_registry ht; exact h
  | iteThenMatched _ _ _ ht => have h := terminatesTo_preserves_registry ht; exact h
  | iteElseMatched _ _ _ ht _ => have h := terminatesTo_preserves_registry ht; exact h
  | iteThenStd _ _ ht => have h := terminatesTo_preserves_registry ht; exact h
  | iteElseStd _ _ ht _ => have h := terminatesTo_preserves_registry ht; exact h
  | appFun _ ht => have h := terminatesTo_preserves_registry ht; exact h
  | appFnBody _ ht2 _ ht1 =>
      have h1 := terminatesTo_preserves_registry ht1
      have h2 := terminatesTo_preserves_registry ht2
      exact h1.trans h2
  | appPfnBody _ ht2 _ ht1 =>
      have h1 := terminatesTo_preserves_registry ht1
      have h2 := terminatesTo_preserves_registry ht2
      exact h1.trans h2
  | _ => rfl

/-- The steps reachable from a root run under the root's registry. -/
theorem Reach.registry_eq {root s : Step} (h : Reach root s) :
    s.cfg.registry = root.cfg.registry := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact (SubStep.registry_eq hstep).trans ih

/-- An extern call looks its implementation up in the registry of its step. -/
theorem ExternCallAt.registry_get {s : Step} {effects : List Effect} {entry : ExternCallEntry}
    {res : TypeResult} {cf : Config} {o : Value}
    (h : ExternCallAt s effects entry res cf o) :
    ∃ id impl, s.cfg.registry.get? id = some impl := by
  cases h with
  | pfn _ ht2 _ ht1 _ _ hget =>
      have h1 := terminatesTo_preserves_registry ht1
      have h2 := terminatesTo_preserves_registry ht2
      rw [h1.trans h2] at hget
      exact ⟨_, _, hget⟩
  | fn _ ht2 _ ht1 _ _ _ hget =>
      have h1 := terminatesTo_preserves_registry ht1
      have h2 := terminatesTo_preserves_registry ht2
      rw [h1.trans h2] at hget
      exact ⟨_, _, hget⟩

/-- A run under a registry without entries makes no extern call. -/
theorem ExternCallAt.not_of_registry_none {root s : Step} {effects : List Effect}
    {entry : ExternCallEntry} {res : TypeResult} {cf : Config} {o : Value}
    (hnone : ∀ id, root.cfg.registry.get? id = none) (hs : Reach root s) :
    ¬ ExternCallAt s effects entry res cf o := by
  intro hcall
  obtain ⟨id, impl, hget⟩ := hcall.registry_get
  rw [Reach.registry_eq hs, hnone id] at hget
  cases hget

/-- An `extern val` declaration looks its value up in the registry of its
    step. -/
theorem ExternValAt.registry_get {s : Step} {res : TypeResult} {cf : Config} {o : Value}
    (h : ExternValAt s res cf o) : ∃ id impl, s.cfg.registry.get? id = some impl := by
  cases h with
  | @mk ctx _ _ _ _ _ _ _ _ _ _ ht =>
      obtain ⟨impl, hrun⟩ :=
        ExternDeclBoundaryRun.of_terminatesTo_externVal (ctx := ctx) (res := res) ht
      exact ⟨_, _, hrun.run.lookup⟩

theorem ExternValAt.not_of_registry_none {root s : Step} {res : TypeResult} {cf : Config}
    {o : Value} (hnone : ∀ id, root.cfg.registry.get? id = none) (hs : Reach root s) :
    ¬ ExternValAt s res cf o := by
  intro hval
  obtain ⟨id, impl, hget⟩ := hval.registry_get
  rw [Reach.registry_eq hs, hnone id] at hget
  cases hget

/-- *Match* holds for a run under a registry without entries. -/
theorem ExternCallsMatch.of_registry_none {predSat : PredSat} {root : Step}
    (hnone : ∀ id, root.cfg.registry.get? id = none) : ExternCallsMatch predSat root :=
  ⟨fun _ _ _ _ _ _ hs hcall => (ExternCallAt.not_of_registry_none hnone hs hcall).elim,
   fun _ _ _ _ hs hval => (ExternValAt.not_of_registry_none hnone hs hval).elim⟩

/-- *Agreement* holds for two runs under a registry without entries. -/
theorem ExternCallsAgree.of_registry_none {root₀ root₁ : Step}
    (hnone : ∀ id, root₀.cfg.registry.get? id = none) : ExternCallsAgree root₀ root₁ :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hs₀ _ _ _ _ hcall₀ _ _ =>
    (ExternCallAt.not_of_registry_none hnone hs₀ hcall₀).elim⟩
