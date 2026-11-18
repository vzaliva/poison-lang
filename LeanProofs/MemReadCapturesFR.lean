import LeanProofs.ExternProofs
import LeanProofs.ExternRegimeInt

/-!
# Program-level fault-robustness for a *memory-read* (`!r`) `captures:` dependency

This is the capstone for memory-read read-dependencies.  Where `MaxCurriedFR`
exercises an
environment capture and `GuardedCapturesFR` a guarded environment capture, here
the memory-read extern `@23` takes a reference argument `r : ref int` and
declares a *bang* read dependency on the cell behind it:
`captures: { !r :> (int :> clean {}) }`.

The trusted contract is `builtinMemDerefSpec` (a complete five-field
`ExternBoundarySpec`).  Its relational `callFR` field, `builtinMemDeref_callFR`,
carries the memory-read-specific obligation: it composes the *argument condition*
`(ref int :> clean {})` — which forces the two runs to realise `r` to a **common
logical cell** (`agreeValueUnder_ref_common_loc`) — with the *capture*
`!r :> (int :> clean {})` — which forces that cell's **contents** clean, so the
two dereferences agree (`agreeOnClean` on the location side,
`agreeLocUnder.agree_values`).  Both gates are load-bearing: a clean reference
may point to a poisoned cell, so the capture is exactly the extra fact a
memory-read read-dependency contributes to fault-robustness.

Composing the registry-agreement witness with
`TypeSystemEnforcesFaultRobustness_at` discharges the per-context trust premise
and yields program-level fault-robustness for the registry `[@23 memread]` at the
empty context.

The program here is the bare `@23` declaration node (mirroring
`MaxCurriedFR.maxCurried_FR` and `GuardedCapturesFR.guardedCaptures_FR`): it
establishes that the memory-read trusted spec is a registry entry that agrees
with the program's reachable declarations.  The *applied/routed* counterpart —
`MemReadCapturesFR.appliedMemReadCaptures_FR` — additionally materialises a clean
cell with `ref` and routes the `callFR` through a real application; see that
theorem below.
-/

open Std LeanPoison ExternProofs ExternRegimeInt

namespace MemReadCapturesFR

/-- The bare memory-read declaration node: `@23` taking a reference argument `r`
    and declaring the bang read dependency `captures: { !r :> (int :> clean {}) }`. -/
def memReadProg : Expr :=
  Expr.externPfn 23 "r" (Typ.ref Typ.int) false SyntaxPredicate.noPred builtinMemDerefRetSpec
    [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩]

/-- Trusted registry holding the memory-read extern with its complete
    `ExternBoundarySpec`. -/
def memReadRegistry : TrustedRegistry :=
  [⟨builtinMemDerefDecl, builtinMemDerefImpl, builtinMemDerefSpec⟩]

/-- The single declaration syntactically reachable in `memReadProg` — the
    top-level `@23` `externPfn` node, `captures = [!r]` — is matched by the
    registry.  The `simple int` return carries no further nested extern. -/
private theorem memRead_agreesWithProgram :
    TrustedRegistryAgreesWithProgram memReadProg memReadRegistry := by
  intro id d entry hprog hlookup
  unfold memReadProg at hprog
  cases hprog with
  | externPfn =>
      have hl : TrustedRegistry.lookup? memReadRegistry 23
          = some ⟨builtinMemDerefDecl, builtinMemDerefImpl, builtinMemDerefSpec⟩ := by
        simp [memReadRegistry, TrustedRegistry.lookup?, builtinMemDerefDecl]
      rw [hl] at hlookup
      cases hlookup
      rfl
  | externPfn_return hret =>
      -- The `@23` return is `simple int`, which carries no nested extern.
      cases hret

/-- Per-context trust premise at the canonical empty initial context. -/
private theorem memRead_hagrees :
    TrustedRegistryAgreesWithReachable memReadProg openEmptyCtx memReadRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) memRead_agreesWithProgram

/-- **Program-level fault-robustness for a memory-read (`!r`) `captures:`
    dependency.**  Composing the registry-agreement witness with the top-level FR
    theorem yields the FR conclusion for the `[@23 memread]` registry at the empty
    context.  The trusted `builtinMemDeref_callFR` inside the registry's spec is
    the memory-read call-boundary obligation: a clean reference argument fixes the
    shared cell, the `!r` capture fixes its contents, and the two dereferences are
    forced to agree across runs. -/
theorem memReadCaptures_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry memReadRegistry)
      memReadProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at memReadRegistry memReadProg s obs openEmptyCtx
    memRead_hagrees

/-! ## Fully exercised: the applied program `@23 (ref 3)`

`memReadCaptures_FR` above is over the bare `@23` declaration node.  The *applied*
program below additionally materialises a clean memory cell with `ref 3` and
applies `@23` to it, so the generic FR theorem routes that application through the
registry's `builtinMemDerefSpec.callFR` — the memory-read gate (reference-clean
argument ⇒ common cell; `!r`-clean capture ⇒ agreeing contents).  Crucially, a
*clean* memory cell is trivially materialisable with `ref`, so — unlike the
guarded environment-capture path, which needs a trusted guarded-value producer —
the memory-read call boundary can be routed through a real application here,
as for the environment capture in `MaxCurriedFR.appliedMaxCurried_FR`.

The reachable declarations are exactly `@23`: the function position is the
`externPfn` node; the argument `ref 3` is a `newRef` of a numeral, which carries
no extern declaration. -/

/-- Applied memory-read: `(extern pfn @23 r : (ref int :> clean {}) -> (int :>
    clean {}), captures: { !r :> (int :> clean {}) }) (ref 3)`.  Applying `@23`
    to the freshly-allocated clean cell routes the FR derivation through the
    memory-read `callFR`. -/
def appliedMemReadProg : Expr :=
  Expr.app
    (Expr.externPfn 23 "r" (Typ.ref Typ.int) false SyntaxPredicate.noPred builtinMemDerefRetSpec
      [⟨CaptureTarget.memVar "r", Typ.int, false, SyntaxPredicate.noPred⟩])
    (Expr.newRef (Expr.num 3))

/-- The reachable declarations of the applied program are exactly `@23`, matched
    by its registry entry.  The function position reaches it (`@23` via
    `externPfn`); the argument `ref 3` reaches none (`newRef` of a numeral). -/
private theorem appliedMemRead_agreesWithProgram :
    TrustedRegistryAgreesWithProgram appliedMemReadProg memReadRegistry := by
  intro id d entry hprog hlookup
  unfold appliedMemReadProg at hprog
  cases hprog with
  | app_fun hb1 =>
      cases hb1 with
      | externPfn =>
          have hl : TrustedRegistry.lookup? memReadRegistry 23
              = some ⟨builtinMemDerefDecl, builtinMemDerefImpl, builtinMemDerefSpec⟩ := by
            simp [memReadRegistry, TrustedRegistry.lookup?, builtinMemDerefDecl]
          rw [hl] at hlookup
          cases hlookup
          rfl
      | externPfn_return hret => cases hret
  | app_arg hb1 =>
      -- `ref 3` = `newRef (num 3)`: no extern declarations.
      cases hb1 with
      | newRef hb2 => cases hb2

/-- Per-context trust premise for the applied program at the empty context. -/
private theorem appliedMemRead_hagrees :
    TrustedRegistryAgreesWithReachable appliedMemReadProg openEmptyCtx memReadRegistry :=
  agreesWithReachable_of_emptyVarEnv (by rfl) appliedMemRead_agreesWithProgram

/-- **Fully-exercised program-level FR for the applied memory-read extern.** For
    the program `@23 (ref 3)`, the trusted registry agrees with the reachable
    decls, so `TypeSystemEnforcesFaultRobustness_at` yields fault-robustness — and
    because the program applies `@23`, the derivation routes that application
    through `builtinMemDerefSpec.callFR` (the memory-read read-dependency gate). -/
theorem appliedMemReadCaptures_FR (s : InputSpec) (obs : ObservableSpec) :
    FaultRobustnessSpecForCtx
      (TrustedRegistry.toRuntimeRegistry memReadRegistry)
      appliedMemReadProg s obs openEmptyCtx :=
  TypeSystemEnforcesFaultRobustness_at memReadRegistry appliedMemReadProg s obs openEmptyCtx
    appliedMemRead_hagrees

/-- The tests of every run of `memReadProg` agree with every view: the
    declaration node has no step below it. -/
theorem memReadCaptures_tests (β : BindVals) (fuel : Nat) (cfg : Config) :
    TestsAgreeWithView β ⟨openEmptyCtx, memReadProg, fuel, cfg⟩ :=
  testsAgreeWithView_of_leaf (fun _ h => by cases h) (fun h => by cases h)

/-- The expressions of the steps a run of `appliedMemReadProg` reaches. The
    callee is a closure of a pure extern, whose body is no pure expression, so
    the call enters no body. -/
private inductive AppliedMemReadExpr : Expr → Prop
  | prog : AppliedMemReadExpr appliedMemReadProg
  | callee : AppliedMemReadExpr memReadProg
  | ref : AppliedMemReadExpr (.newRef (.num 3))
  | num : AppliedMemReadExpr (.num 3)

/-- The tests of every run of `appliedMemReadProg` agree with every view: the
    run reaches no conditional. -/
theorem appliedMemReadCaptures_tests (β : BindVals) (fuel : Nat) (cfg : Config) :
    TestsAgreeWithView β ⟨openEmptyCtx, appliedMemReadProg, fuel, cfg⟩ :=
  testsAgreeWithView_of_closed (fun s => AppliedMemReadExpr s.e) .prog
    (fun {s _} hs h => by
      obtain ⟨_, _, _, _⟩ := s
      cases hs with
      | prog =>
          cases h with
          | appArg => exact .ref
          | appFun _ _ => exact .callee
          | appFnBody _ _ _ hr1 _ _ => cases terminatesTo_externPfn_value hr1
          | appPfnBody _ _ _ hr1 _ hpe _ =>
              obtain ⟨-, rfl, -⟩ := Value.peClosure.inj (terminatesTo_externPfn_value hr1)
              cases hpe
      | callee => cases h
      | ref => cases h with | newRef => exact .num
      | num => cases h)
    (fun {s _ _ _} hs => by
      obtain ⟨_, _, _, _⟩ := s
      cases hs <;> (intro h; cases h))

end MemReadCapturesFR
