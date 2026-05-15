# Extern Regime Handling — Working Notes

Status: **analysis / planning placeholder**. This note isolates the regime
issue for extern-produced predicates from the broader extern poison discussion
in `doc/extern-poison.md`.

## 1. Problem Description

Extern return and effect specifications may introduce predicates intended to act
as latent de-poisoning markers. For example, an `open`-style extern may return a
poisoned integer where `ret >= 0` means the value is a valid file descriptor and
can safely be treated as clean after a matching runtime check.

The current implementation allocates fresh concrete guard tags for extern
predicates at the extern use site. The fault-robustness guard regime, however,
is defined only over tags that appear in the initial critical-input
specification. Tags allocated while typechecking an extern call are therefore
outside the admissible regime domain.

As a result, downstream checks can syntactically match an extern-produced
predicate, but the fault-robustness theorem cannot use the regime to de-poison
the value. The typechecker falls back to the conservative conditional path when
the fresh tag is absent from the regime, and the joined result remains poisoned.

## 2. Analysis

This appears to be a real expressiveness limitation rather than a soundness
bug. The current behavior is conservative: values remain poisoned unless they
are clean outright or their guard tag is known true in the regime.

The limitation matters because extern-produced predicates are meant to describe
facts established at the boundary and later consumed by ordinary Poison checks.
Without a way for the regime to talk about those tags, return predicates on
externs are mostly decorative for fault-robustness. They can affect ordinary
typechecker behavior under manually supplied concrete regimes, but those
regimes are not generally admissible under the public FR theorem.

The motivating `open` case exposes the problem clearly:

- `open` may return `-1` or a nonnegative file descriptor.
- The returned value should remain poisoned until checked.
- After `fd >= 0`, downstream code should be able to treat `fd` as clean.
- Under the current FR regime model, the fresh return tag for `fd >= 0` is not
  part of the regime domain, so the check cannot justify FR-level de-poisoning.

This issue likely affects both immediate extern returns and memory cells written
by extern effects when those writes install fresh predicates.

## 3. Planning Resolution

Placeholder for the resolution plan.

Open design directions to evaluate:

- Extend the admissible regime domain beyond initial critical-input tags to
  include selected tags allocated during typechecking, especially trusted extern
  output tags.
- Define the consistency obligation for those internal tags: what runtime fact
  makes `R(k) = true` or `R(k) = false` meaningful for an extern-produced value?
- Update the trusted-extern boundary contract so extern proofs establish the
  required value-level relationship for any tags they introduce.
- Revisit the FR theorem statement and proof plumbing so the extended regime is
  threaded through typechecking, boundary proofs, and observable agreement.
- Decide whether extern return predicates and extern effect predicates should
  share the same mechanism or require separate treatment.

