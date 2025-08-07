### SVD'25 Talk proposal

We present ongoing work on Poison-lang, a typestate system designed for formal
fault propagation analysis with selective sanitisation (termed "de-poisoning").
The language tracks data faults, which we call "poison", that may arise from
potential hardware or software failures, using a static, flow-sensitive type
system that facilitates principled sanitisation through guard-tagged predicates.
The design combines a two-point poison lattice with region-parameterised
reference types that separate pointer from payload reliability, a typestate map
joined at control-flow merge points, and higher-order functions whose typing
closures prevent taint from being hidden behind abstraction; a three-level type
hierarchy (surface, enriched, qualified) cleanly separates the user interface,
runtime, and analysis artefacts. We will give a high-level account of the
theory: operational semantics and definitional interpreter in Lean 4, and
guard-aware typing rules, together with formal properties, we aim to prove such
as poison irrelevance, non-interference, soundness, as well as progress, and
preservation. A key practical contribution is that our prototype typechecker can
analyse existing code to conservatively identify fault flows and pinpoint
opportunities for de-poisoning under verified guards, offering a fail-safe
integrity guarantees without changing runtime behaviour. This work is being
conducted at Tufts University's TuPL group as part of a larger DARPA-funded
programme addressing both software and hardware fault detection and recovery.


Talk Duration: 20 min
Presenter: Vadim Zaliva <Vadim.Zaliva@tufts.edu>
