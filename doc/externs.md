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
**Trust:** Missing default trusted spec

**Canonical declaration (guarded-input example used in tests):**

```poison
extern pfn @19 x : (int :> clean { t, v => (v >= 0) }) -> ((int :> clean {}))
```

**Implementation:** Currently computes `Nat.sqrt n.toNat`; non-integer
arguments fail at dispatch. This should be changed to the explicit guarded
definition `if x >= 0 then Lean.sqrt x else 0` (for integer `x`). The negative
case is semantically important even though the current `toNat` route is close
operationally: it exposes the constant-output branch needed by the boundary
proof.

**Boundary contract (intended, not yet proved):** Always clean integer result,
with a two-case FR proof. If both runs satisfy `x >= 0`, the guarded clean input
condition forces matching arguments, so the square-root results match. If both
runs fail `x >= 0`, the arguments need not match, but both executions return
`0`. See `examples/extern_arg_precond_sqrt.poison`. A trusted spec is still
needed before `@19` can appear in a `TrustedRegistry` used by the public FR
theorem.

## `@21` — `errno` (extern value)

**Kind:** `extern val`  
**Trust:** Missing default trusted spec

**Canonical declaration:**

```poison
extern val @21 : (ref int :> clean {})
```

**Implementation:** Driver-supplied reference to address `1000000`, initial cell
value `0` in `defaultInitialState`.

**Boundary contract (intended, not yet proved):** Initialized ref-valued extern;
pairs with `@22` write effects. A trusted spec also needs an initial-state /
address-cursor story: the executable default puts `errnoAddr` above the current
`nextAddr`, while proof-side `wfConfig` and `ExternOperationalSafe` require stored
reference values to be below the consumer's `nextAddr`. No trusted val spec yet.

## `@22` — `set_err` (impure)

**Kind:** `extern fn`  
**Trust:** Missing default trusted spec

**Canonical declaration:**

```poison
let errno = extern val @21 : (ref int :> clean {}) in
extern fn @22 n : (int :> clean {}) -> ((unit :> clean {})),
  effects: { !errno :> (int :> clean {}) }
```

Programs may also declare additional `captures:` read dependencies (see
`examples/extern_fn_captures_clause.poison`); the shipped implementation only
writes `!errno`.

**Implementation:** Writes integer `n` into the `errno` cell; returns `unit`;
does not allocate (`nextAddr` unchanged).

**Boundary contract (intended, not yet proved):** Impure update of a declared
effect cell. A trusted spec must cover both the immediate `unit` return and the
post-state of `!errno` under the declared `effects:` block. Because `setErrImpl`
writes the fixed `errnoAddr` without bumping `nextAddr`, trusted operational
safety also needs the same address-cursor invariant as `@21`; it is not the
universal no-allocation shape of an identity shim. This is the natural trusted
`extern fn` example for capture- and effect-bearing fn specs.

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
| `@21` | val | ref at `errnoAddr` | **missing** |
| `@22` | fn | `setErrImpl` | **missing** |
| `@19` | pfn | `sqrtImpl` | **missing** |
| `@23` | pfn | `memDerefImpl` | `builtinMemDerefSpec` |

User programs may declare the same ids with richer `captures:` / `effects:`
clauses; dispatch uses the fixed implementations above. Ids not in this map fail
at runtime. The default trusted registry should prove the listed shipped
declarations directly; specialised same-id proof variants, such as guarded
`@11`, remain auxiliary examples rather than alternatives to the shipped entry.
