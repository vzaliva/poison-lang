# Shipped extern registry

Status: reference for the interpreter's fixed built-in extern set
(`LeanPoison/ExternBuiltins.defaultRegistry`). Each entry below gives a
canonical surface declaration, a short implementation summary, and the
fault-robustness (FR) boundary status.

Related documents:

- `doc/ffi-proposal.md` — FFI roadmap and `captures:` / `effects:` model.
- `doc/extern-poison.md` — argument preconditions, regimes, trust triage.
- `doc/ffi-axioms.md` — proof-facing `ExternBoundarySpec` and `TrustedRegistry`.
- `doc/poison-interpreter.md` — CLI and default runtime registry.

## Shipped-entry proof obligation

Every shipped extern should have both:

- a runtime entry in `LeanPoison/ExternBuiltins.defaultRegistry`; and
- a matching trusted entry in the default trusted registry.

Entries still marked as missing trusted evidence below are cleanup gaps, not a
separate "runtime-only" category of shipped extern.

A trusted entry's boundary contract is an `ExternBoundarySpec` with five fields:

- **`declFR` / `callFR`** — paired-run FR obligations at declaration and call
  boundaries.
- **`declSingle` / `callSingle`** — masked single-run counterparts used by the
  step proof.
- **`operational`** — `ExternOperationalSafe`: well-formed outputs, preserved
  config well-formedness, and `nextAddr` monotonicity where applicable.

Argument-side **preconditions** are the declared argument `QTyp` (for example
`(int :> clean {})`). **Read dependencies** are declared in `captures:`; **write
effects** in `effects:` (impure `extern fn` only). Argument preconditions and
`captures:` are checked together at call entry under the active regime. Effects
are post-state memory summaries: after the call gate succeeds, the typechecker
resolves and applies them to the memory typing, and the trusted boundary proof
must justify the resulting post-state.

## max/2

The shipped curried pair `@10` / `@11` simulates binary `max : int × int → int`.
Poison externs are unary (or nested-returning), so two-argument `max` is
expressed as currying: the outer stage `@10` fixes the first argument `a` and
returns an inner `@11` closure; applying that closure to `b` yields `max a b`.
Typical use:

```poison
let m =
  extern pfn @10 a : (int :> clean {}) -> (
    extern pfn @11 b : (int :> clean {}) -> ((int :> clean {})),
      captures: { a :> (int :> clean {}) }
  )
in (m 7) 2   -- 7
```

**Kind:** two `extern pfn` entries (`@10` outer, `@11` inner)  
**Trust:** Trusted (`ExternProofs.builtinMax10Spec`,
`ExternProofs.builtinMax11CapturesSpec`; program FR in
`LeanProofs/MaxCurriedFR.lean`)

**Boundary contract (combined):** Clean integers at both stages; clean integer
result. The outer call returns a nested `@11` closure capturing `a`. The inner
call reads `a` from the environment (declared via `captures:` on `@11`) and
combines it with argument `b`. Program-level FR is proved for `(m 7) 2`.

### Outer — `@10`

**Canonical declaration:**

```poison
extern pfn @10 a : (int :> clean {}) -> (
  extern pfn @11 b : (int :> clean {}) -> ((int :> clean {})),
    captures: { a :> (int :> clean {}) }
)
```

**Implementation:** On an integer runtime argument `a`, returns the inner `@11`
pure closure capturing the call environment (which holds `a`). Cleanness is the
trusted boundary contract, not a runtime branch in `outerMaxImpl`.

**Boundary contract:** Clean integer argument in; nested `@11` pfn closure out.
The nested return descriptor matches the `@11` node produced at runtime. No
`captures:` on `@10` itself — the captured-`a` contract is carried on the nested
`@11` return shape and on the capture-bearing `@11` trusted declaration used in
the curried-max registry.

### Inner — `@11`

**Canonical declaration (capture-bearing contract used by FR proofs):**

```poison
extern pfn @11 b : (int :> clean {}) -> ((int :> clean {})),
  captures: { a :> (int :> clean {}) }
```

**Implementation:** Reads captured outer argument `a` from the unified environment
and returns `max a b`.

**Boundary contract:** Clean integer argument `b` plus clean captured `a` (via
`captures:` read dependency). Clean integer result. The relational `callFR` gate
requires both `agreeOnClean` on the body entry (for `a`) and clean agreement on
`b`. A declaration without `captures:` cannot close this call boundary. A
separate guarded-capture proof variant exists (`builtinMax11GuardedSpec`); the
shipped runtime uses the unguarded capture above.

## `@12` — `abs` (pure)

**Kind:** `extern pfn`  
**Trust:** Trusted (`ExternProofs.builtinAbsSpec`)

**Canonical declaration:**

```poison
extern pfn @12 x : (int :> clean {}) -> ((int :> clean {}))
```

**Implementation:** Integer absolute value (`Int.natAbs`).

**Boundary contract:** Clean integer argument required — a declaration with only
`(int) -> (int :> clean {})` is too strong and is ruled out by an obstruction
proof (`builtinAbs_cleanPost_obstruction`). Under the clean-input precondition,
equal clean arguments yield equal absolute values, satisfying clean output
agreement. No `captures:` or `effects:`.

## `@19` — integer `sqrt` (pure)

**Kind:** `extern pfn`  
**Trust:** Missing default trusted spec — **blocked** (see Blocker below)

**Intended canonical declaration (guarded-input example):**

```poison
extern pfn @19 x : (int :> poisoned { t, v => (v >= 0) }) -> ((int :> clean {}))
```

The intended boundary example takes a *guarded poisoned* integer: a value whose
poison is vouched clean exactly when the guard `v >= 0` is active. (The shipped
test `examples/extern_arg_precond_sqrt.poison` currently uses a clean-guarded
variant that typechecks and runs but carries no trusted spec.)

**Implementation:** Computes `Nat.sqrt n.toNat`; non-integer arguments fail at
dispatch. The intended guarded contract would use the explicit form
`if n >= 0 then Int.ofNat (Nat.sqrt n.toNat) else 0`, so the negative branch
is a constant `0`.

**Boundary contract (intended):** Always clean integer result, with a two-case
FR proof. When the guard is active, the argument is clean-under-regime, paired
runs must agree, and the roots match. When the guard is inactive, paired runs
need not agree, but both arguments fail `v >= 0` (are negative) and the
implementation returns `0`.

**Blocker (not provable without trusted-surface expansion).** The inactive-guard
branch is the obstruction. The FR stack is parametric over an abstract predicate
oracle `predSat`, whose only behavioral law (`PredSatLaws`) is `match_iff` — a
*forward* law requiring an evaluated source-level `if` condition (`matchGuard`
recognition plus a `terminatesTo … (bool b)` witness). A guard attached to a
*value* (not an evaluated condition) yields only the abstract
`¬ predSat k μ (num n)` from `varsRegime.withPred_ok`; nothing connects that to
the arithmetic fact `n < 0`. Discharging the inactive branch through the return
spec ("guard inactive ⟹ returns `0`") does not avoid this — it relocates the
same `¬predSat ⟹ n < 0` fact into the trusted layer. A clean-input spec that
pins only the argument poison flag and ignores the predicate compiles, but it is
*not* this example: it silently restricts `@19` to the clean (active-guard)
precondition. A faithful trusted `@19` therefore needs a deliberate
trusted-surface expansion (a `PredSatLaws` guard-body-evaluation law, or a
per-spec arithmetic precondition on the boundary) — a reserved design decision.
Until that is taken, `@19` has no trusted spec.

## `@21` — `errno` (extern reference)

**Kind:** `extern ref`\
**Trust:** Trusted (`ExternProofs.builtinErrnoSpec`; program FR in
`LeanProofs/ExternRegimeInt.lean` — `ExternRegimeInt.errnoExternRef_FR` for
the bare declaration and `ExternRegimeInt.errnoScenario_FR` for the combined
`@21`/`@22` declare/write/read scenario)

**Canonical declaration:**

```poison
extern ref @21 : (ref int :> clean {}), points_to: (int :> poisoned {})
```

The qualifier before `points_to:` describes the returned reference value; the
`points_to:` qualifier describes the pointed-to memory cell. The conservative
poisoned cell assumes nothing about the external cell's initial contents;
cleanness is re-established by writing through the reference (an assignment or
`@22`'s `!errno` write effect). The old ref-typed `extern val` spelling is
rejected. Clean `points_to:` cells are a documented language limitation (see
`doc/extern-write-effects.md`, "Limitation: no clean `points_to:` cells").
`extern ref` declarations are unique per extern id per program and may not
appear under `fn`/`pfn` bodies. The nesting rule is enforced where a body is
typechecked: at declaration for `pfn` (pure bodies are converted via
`toPExpr`, which has no extern-declaration form) and at application for `fn`
(`fn` bodies are typechecked only when applied, so a never-applied `fn` whose
body lexically contains an `extern ref` typechecks and runs — consistent with
the language's deferred `fn`-body typechecking, under which *any* type error
in a never-applied body goes undetected; such a body never evaluates, so the
declaration never takes effect).

**Implementation:** Driver-supplied reference to address `1000000`, initial cell
value `0` in `defaultInitialState`.

**Boundary contract:** Complete five-field `ExternBoundarySpec`
(`ExternProofs.builtinErrnoSpec`, axioms `propext`/`Classical.choice`/
`Quot.sound` only). The declaration fields produce the clean reference to the
registry-reserved address and seed the poisoned `points_to:` cell typing; the
call fields are vacuous (a reference extern is a declaration, not a callable);
operational safety follows from `RegistryReservedWF` (the reserved cell is
present and below the cursor in every run). The realization-map crux —
injectivity of the θ-insert at the declaration — is discharged by the
`ReservedDiscipline` invariant threaded through the step theorem rather than
by a `wfConfig` fold.

## `@22` — `set_err` (impure)

**Kind:** `extern fn`  
**Trust:** Trusted (`ExternProofs.builtinSetErrSpec`; program FR in
`LeanProofs/ExternRegimeInt.lean`)

**Canonical declaration:**

```poison
let errno =
  extern ref @21 : (ref int :> clean {}), points_to: (int :> poisoned {})
in
extern fn @22 n : (int :> clean {}) -> ((unit :> clean {})),
  effects: { !errno :> (int :> clean {}) }
```

Programs may also declare additional `captures:` read dependencies (see
`examples/extern_fn_captures_clause.poison`); the shipped implementation only
writes `!errno`.

**Implementation:** Writes integer `n` through the `errno` reference resolved
from the extern closure's captured environment; in the shipped `@21`/`@22`
scenario that reference is the driver-supplied `errnoAddr` cell. Returns `unit`;
does not allocate (`nextAddr` unchanged).

**Boundary contract:** Complete five-field `ExternBoundarySpec`. The declaration
fields cover the produced extern closure. The call fields cover the immediate
`unit` return and the typed post-state of the declared `effects:` block,
`!errno :> (int :> clean {})`. Operational safety follows from the well-formed
captured `errno` reference and the insertion-only memory update.
`ExternProofs.defaultRegistry_lookup_seterr` connects the interpreter's shipped
`defaultRegistry` entry to the proven `setErrImpl`.

The combined source scenario that first declares `@21` and then declares/calls
`@22` is proven end to end: `ExternRegimeInt.errnoScenario_FR` instantiates
the top-level theorem at the two-entry trusted registry.

## `@23` — `memDeref` (pure, memory read)

**Kind:** `extern pfn`  
**Trust:** Trusted (`ExternProofs.builtinMemDerefSpec`; program FR in
`LeanProofs/MemReadCapturesFR.lean`)

**Canonical declaration:**

```poison
extern pfn @23 r : (ref int :> clean {}) -> ((int :> clean {})),
  captures: { !r :> (int :> clean {}) }
```

**Implementation:** Dereferences reference argument `r` and returns the cell's
integer contents.

**Boundary contract:** Representative explicit-reference memory-read path. The
argument condition `(ref int :> clean {})` fixes the logical cell across paired
runs; the bang capture `!r :> (int :> clean {})` fixes cell contents clean so
two reads agree. Relational `callFR` composes reference agreement with capture
satisfaction. A clean reference may point at a poisoned cell, so the capture is
load-bearing.

## Default shipped registry

`LeanPoison/ExternBuiltins.defaultInitialState` currently registers the shipped
runtime entries below. The intended invariant is that the default trusted
registry contains the same shipped ids with matching declarations and
`ExternBoundarySpec` evidence. Rows marked **missing** identify the remaining
proof/registry work.

| Id | Kind | Runtime implementation | Trusted evidence |
| --- | --- | --- | --- |
| `@10` | pfn | `outerMaxImpl` | `builtinMax10Spec` |
| `@11` | pfn | `innerMaxImpl` | `builtinMax11CapturesSpec` |
| `@12` | pfn | `absImpl` | `builtinAbsSpec` |
| `@21` | ref | ref at `errnoAddr` | `builtinErrnoSpec` |
| `@22` | fn | `setErrImpl` | `builtinSetErrSpec` |
| `@19` | pfn | `sqrtImpl` | **missing** |
| `@23` | pfn | `memDerefImpl` | `builtinMemDerefSpec` |

User programs may declare the same ids with richer `captures:` / `effects:`
clauses; dispatch uses the fixed implementations above. Ids not in this map fail
at runtime. The default trusted registry should prove the listed shipped
declarations directly; specialised same-id proof variants, such as guarded
`@11`, remain auxiliary examples rather than alternatives to the shipped entry.
