# Extern Reserved-Address Invariant Proposal

## Problem

The default extern registry includes two representative stateful externs:

- `@21`, `errno`, is an extern value implemented as `Value.loc errnoAddr`.
- `@22`, `set_err`, is an impure extern intended to write the cell named by
  the lexical `errno` binding and return `unit` without changing `nextAddr`.

The intended source-level shape is:

```poison
let errno = extern val @21 : (ref int :> clean {}) in
extern fn @22 n : (int :> clean {}) -> ((unit :> clean {})),
  effects: { !errno :> (int :> clean {}) }
```

The current operational safety contract is quantified over every `wfConfig`.
For `@21`, proving that `Value.loc errnoAddr` is well formed requires
`errnoAddr < cfg.nextAddr`.

Current `wfConfig` only says that existing memory keys and environment values
are below `nextAddr`. It does not say that extern-reserved addresses exposed by
the registry are below `nextAddr`. Therefore the proof obligation for `@21` is
false for well-formed configs with small `nextAddr`.

The current `setErrImpl` also writes the fixed `errnoAddr` directly. This
should be changed so `@22` follows its declared lexical effect target:
look up `errno` in the captured runtime environment, require it to be a
reference, and write that referenced address.

There is also a pre-existing initial-state gap independent of this proposal.
`defaultInitialState.memory` already contains `errnoAddr`, while
`defaultInitialState.nextAddr` is `0`. The current `wfConfig` memory-bound
conjunct therefore already rejects the shipped default state, because
`errnoAddr < 0` is false. The reserved-address invariant does not introduce
that cost; it makes the same inconsistency explicit from the registry side.

## Analysis

The missing invariant is not an input-spec or extern-regime fact.
`InputSpec.regimeExterns` selects which extern-generated predicate tags are
included in the fault regime. It does not describe concrete runtime resources.

The `effects:` block is also not sufficient by itself. For `@22` it says, at the
type level, that the extern modifies `!errno`. That is useful for relational
fault-robustness, but it also fixes the intended runtime target: the
implementation should write the same lexical reference that the typechecker
uses for the effect.

For the current examples, the concrete reserved address can be derived from the
runtime registry itself: an address is reserved when the registry exposes it as
an extern value. This is preferable to deriving it from memory membership:
the registry is fixed during evaluation, while memory changes. A
registry-relative invariant is preserved by the existing `nextAddr`
monotonicity story; a memory-membership invariant would require extra
threading that the reserved cell stays allocated.

The key proof issue for `@21` is quantifier scope. The needed fact is relative
to the registry carried by the config, so it must be available inside the
operational-safety quantifiers.

For `@21`, the registry-level hook already exists. The `RegistryOperationalSafe`
`val` clause receives both `cfg : Config` and `cfg.registry = reg`, but the
current `TrustedRegistry.operationalSafe` bridge discards that equality and
routes through the unconditional per-entry `ExternOperationalSafe` `val`
clause. That per-entry `val` clause is too strong: a stored `Value.loc a` cannot
be well formed for every `wfConfig`, only for configs whose registry/resource
invariant bounds `a` below `nextAddr`.

For `@22`, the implementation should not need the registry-reserved-address
fact. The runtime already passes the unified captured environment to impure
extern implementations. If `setErrImpl` resolves `errno` from that environment
and writes the resulting location `a`, then the existing `wfVarEnv addr env`
premise gives `a < addr`. The operational proof becomes the same shape as an
ordinary environment-targeted reference write, and the runtime write matches the
lexical `effects:` target.

## Proposed Solution

Derive reserved runtime addresses from the registry:

```lean
ReservedAddr reg a :=
  exists id, reg.get? id = some (ExternImpl.val (Value.loc a))
```

Then define the compatibility invariant:

```lean
RegistryReservedBelow reg next :=
  forall a, ReservedAddr reg a -> a < next
```

Fold this into runtime configuration well-formedness:

```lean
wfConfig cfg :=
  MemoryBelowNext cfg.memory cfg.nextAddr
  and wfVarEnv cfg.nextAddr cfg.varEnv
  and RegistryReservedBelow cfg.registry cfg.nextAddr
```

A config is then well formed relative to the registry it carries only when all
registry-exposed reserved locations are below its address cursor. This narrows
the public fault-robustness theorem's domain to configs satisfying the
registry-resource invariant. That is intentional: the old domain included
configs for which `@21` operational safety is false.

With that invariant:

- `@21`'s `Value.loc errnoAddr` is well formed because `errnoAddr` is derived
  from the registry entry for `@21`.

Separately, `@22`'s memory update is well formed because the proposed
implementation writes the location resolved from the captured `errno` binding,
and `wfVarEnv` bounds that location below the current address cursor.

`setErrImpl` should therefore become a lexical-target implementation:

```lean
setErrImpl env (Value.num n) mem next :=
  match VarEnv.lookup env "errno" with
  | some (Value.loc a) => .ok (Value.unit, Memory.update mem a n, next)
  | _ => .error ...
```

In the intended example, the lexical `errno` binding comes from `@21`, so the
resolved location is `errnoAddr`. If a program binds `errno` to a different
reference, `set_err` writes that lexical target instead, matching the
`effects: { !errno ... }` declaration.

For `@21`, the corresponding change is smaller: use the existing
`cfg.registry = reg` premise in the registry-level `val` bridge, and weaken the
per-entry `val` obligation so it is not an impossible unconditional
`forall cfg, wfConfig cfg -> wfValue cfg.nextAddr v`.

The default initial state must satisfy both the existing memory-bound invariant
and the new registry-reserved-address invariant. If `errnoAddr` remains
`1000000`, then `defaultInitialState.nextAddr` must be at least
`errnoAddr + 1`. This is already required by the current memory contents, not
just by the proposed registry invariant. If preserving low program-visible
allocation addresses is more important, that requires a larger design where
reserved addresses live outside the normal `nextAddr` high-water mark; this
proposal intentionally avoids that larger change.

## Implementation Checkpoints

This is a trusted extern boundary mechanism change and should not be
implemented without explicit approval.

1. Fix the shipped default initial state independently: either raise
   `defaultInitialState.nextAddr` above `errnoAddr` or move the `errno` cell out
   of ordinary memory. Update the existing comment that says `nextAddr` remains
   `0` because `errnoAddr` is above the program-visible range.
2. Add `ReservedAddr` / `RegistryReservedBelow` and fold the latter into
   `wfConfig`. Re-establish preservation using registry immutability and
   `nextAddr` monotonicity.
3. Repair the `val` bridge: consume the existing `cfg.registry = reg` premise,
   and weaken the impossible unconditional per-entry `val` obligation. This is
   the focused @21 step.
4. Change `setErrImpl` to resolve `"errno"` from the captured runtime
   environment and write that location. Prove its operational safety from the
   existing `wfVarEnv addr env` premise.

## Related Limitations

The executable registry is keyed by extern id, not by source name. There is no
global registry-provided `errno` name. The `effects:` target is a source-level
name resolved lexically from the captured type environment: `!errno` is looked
up as `errno` in the extern callable's unified environment, with no registry
fallback.

The intended example therefore binds the name explicitly:

```poison
let errno = extern val @21 : (ref int :> clean {}) in
extern fn @22 n : (int :> clean {}) -> ((unit :> clean {})),
  effects: { !errno :> (int :> clean {}) }
```

If `@22` is declared with `effects: { !errno ... }` and no lexical `errno` is in
scope, the effect target has no source meaning and should fail when the effect
is applied. With the proposed lexical-target implementation, if a source
program instead binds `errno` to an ordinary reference, for example
`let errno = ref 0`, both the type-level effect and the runtime write target
that local reference.

This proposal uses the conventional source name `"errno"` in the representative
`@22` implementation. A more general future mechanism could make effect-target
selection explicit in the extern implementation interface instead of relying on
a hard-coded source name.

## Scope Note

This derived approach covers the representative reserved-value pattern we
currently need: an extern value exposes a top-level `.val (Value.loc a)` entry
in the registry. Locations hidden in other stored extern values, such as closure
environments, are not reserved by the
`ReservedAddr` definition above. If later trusted externs write hidden reserved
cells not exposed through a top-level `.val (Value.loc a)`, then explicit
reserved-address metadata or a broader derived definition would be needed at
that point. Every top-level registry `val` location also raises the minimum
well-formed initial `nextAddr`.
