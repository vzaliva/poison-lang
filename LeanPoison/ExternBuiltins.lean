import LeanPoison.Syntax
import LeanPoison.Runtime

/-!
# Built-in extern implementations (shared runtime core)

The interpreter ships with a fixed, publicly documented set of externs that unit
tests may invoke by their well-known identifiers:

  * `@10` : outer pure-fn stage of curried `max` (`int -> ...`)
  * `@11` : inner pure-fn stage of curried `max`, expects captured `a` in env
  * `@12` : pure `abs` (`int -> int`)
  * `@19` : pure integer `sqrt`
  * `@21` : extern ref `errno` : `ref int`     (driver-allocated cell, init 0)
  * `@22` : extern fn  `set_err n` : `(int) -> unit`   (writes n into `!errno`)
  * `@23` : extern pfn `memDeref r` : `(ref int) -> int` (reads `!r`; declares the
            memory-read read-dependency `captures: { !r :> (int :> clean {}) }`)

These implementations live here, *below* both the interpreter (`Main.lean`) and
the proof stack (`LeanProofs/`), so that the running interpreter and the
proof-side trusted boundary specs reference the **same** runtime functions:
`ExternProofs.builtinMax10Impl` is *definitionally* `.pfn outerMaxImpl`, etc.
The trusted declarations / `ExternBoundarySpec`s remain proof-side (they are not
executable registry data).

See `doc/externs.md` and `doc/poison-lang-description.tex`.
-/

open Std

/-- Driver-chosen runtime address for the `errno` cell (`@21`). The shipped
    initial state starts `Config.nextAddr` at `errnoAddr + 1`, so
    program-allocated cells follow it (see `DefaultInitialState`). -/
def errnoAddr : Address := 1000000

/-- Outer curried-`max` stage (`@10`): on a clean integer argument, return the
    inner `@11` pure closure capturing the call environment (which holds the
    outer argument `a`).  The inner `@11` argument condition is the source
    declaration of curried `max`'s inner stage: `(int :> clean {})` — an honest
    clean precondition (return descriptor `.simple .int false .noPred`). -/
def outerMaxImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | unifiedEnv, Value.num _a, _m =>
      .ok (Value.peClosure "b"
        (Expr.externPfn 11 "b" .int false .noPred (.simple .int false .noPred) [])
        unifiedEnv)
  | _, _, _ => .error (.implFailure 10 "expected int argument")

/-- Inner curried-`max` stage (`@11`): read the captured outer argument `a` from
    the unified environment and return `max a b`. -/
def innerMaxImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | unifiedEnv, Value.num b, _m =>
      match VarEnv.lookup unifiedEnv "a" with
      | some (Value.num a) => .ok (Value.num (max a b))
      | _ => .error (.implFailure 11 "captured `a` missing or not an int")
  | _, _, _ => .error (.implFailure 11 "expected int argument")

/-- Pure `abs` (`@12`). -/
def absImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | _, Value.num n, _ => .ok (Value.num (Int.ofNat n.natAbs))
  | _, _, _           => .error (.implFailure 12 "expected int argument")

/-- Integer square root (`@19`).  Used by the `sqrt`-style extern
    argument-condition example (`examples/extern_arg_precond_sqrt.poison`): its
    honest clean output relies on the caller-side precondition `x >= 0`, not on a
    runtime branch. -/
def sqrtImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | _, Value.num n, _ => .ok (Value.num (Int.ofNat (Nat.sqrt n.toNat)))
  | _, _, _           => .error (.implFailure 19 "expected int argument")

/-- Memory-read extern (`@23`, the `!r` read-dependency demonstrator): given a
    *reference* argument `r : ref int`, dereference it and return the cell's
    integer contents.  The declared `captures: { !r :> (int :> clean {}) }`
    states that the result reads the memory cell behind `r`.  Combined with the
    `(ref int :> clean {})` argument condition this is exactly enough for
    fault-robustness: the argument condition fixes the reference's *location*
    (both runs realise `r` to a common logical cell), and the capture fixes the
    cell *contents* clean (so the two reads agree).  A clean reference may point
    to a poisoned cell, so the capture is genuinely load-bearing — this is why
    memory-read read-dependencies exist. -/
def memDerefImpl
    : VarEnv → Value → Memory → Except ExternError Value
  | _unifiedEnv, Value.loc addr, mem =>
      match Memory.lookup mem addr with
      | some n => .ok (Value.num n)
      | none   => .error (.implFailure 23 "memDeref: referenced cell missing")
  | _, _, _ => .error (.implFailure 23 "memDeref: expected ref argument")

/-- `set_err n` (`@22`): write `n` into the cell named by the lexical `errno`
    binding and return `unit`.

    Following its declared effect `!errno`, the implementation resolves `errno`
    against the runtime environment it is handed.  Per `beval`'s impure-extern
    dispatch that environment is the *closure-captured* environment of the `@22`
    declaration, extended with the argument — so the write targets whatever
    `errno` denoted at the point `@22` was declared.  A binding that shadows
    `errno` later, in the body that calls `set_err`, lives in the body scope and
    never enters the captured environment, so it cannot retarget the write.  In
    the intended example `errno` is bound by `@21`, so the resolved cell is
    `errnoAddr`.  No new allocation, so `nextAddr` is threaded through unchanged. -/
def setErrImpl
    : VarEnv → Value → Memory → Address →
      Except ExternError (Value × Memory × Address)
  | env, Value.num n, mem, next =>
      match VarEnv.lookup env "errno" with
      | some (Value.loc a) => .ok (Value.unit, Memory.update mem a n, next)
      | _ => .error (.implFailure 22 "set_err: `errno` must be a reference in scope")
  | _, _, _, _ => .error (.implFailure 22 "expected int argument")

/-- Bundled initial runtime state shipped with the interpreter: the registry,
    pre-populated memory (the `errno` cell), and `nextAddr`.

    `nextAddr` starts at `errnoAddr + 1` so the pre-populated `errno` cell — and
    every registry-reserved address — sits strictly below the address cursor.
    This is what makes the shipped state well formed: the `wfConfig` memory bound
    requires every populated address to be below `nextAddr`, and the
    registry-reserved-address invariant requires the same of `errnoAddr`. -/
structure DefaultInitialState where
  memory   : Memory
  nextAddr : Address
  registry : ExternRegistry

/-- Registry/insert helper. `register` failures are impossible here because
    all ids are hard-coded literals; `panic!` is purely defensive. -/
def regInsert (reg : ExternRegistry) (id : ExternId) (impl : ExternImpl)
    : ExternRegistry :=
  match register reg id impl with
  | .ok r => r
  | .error e => panic! s!"defaultInitialState: {e}"

/-- Build the default registry and driver-supplied initial memory/cursor. -/
def defaultInitialState : DefaultInitialState :=
  let mem0 : Memory := Memory.update emptyMemory errnoAddr 0
  let r0 : ExternRegistry := ∅
  let r1 := regInsert r0 10 (.pfn outerMaxImpl)
  let r2 := regInsert r1 11 (.pfn innerMaxImpl)
  let r3 := regInsert r2 12 (.pfn absImpl)
  let r4 := regInsert r3 21 (.val (Value.loc errnoAddr))
  let r5 := regInsert r4 22 (.fn setErrImpl)
  let r6 := regInsert r5 19 (.pfn sqrtImpl)
  let r7 := regInsert r6 23 (.pfn memDerefImpl)
  { memory := mem0, nextAddr := errnoAddr + 1, registry := r7 }

/-- Convenience handle for callers that need only the shipped extern registry. -/
def defaultRegistry : ExternRegistry := defaultInitialState.registry
