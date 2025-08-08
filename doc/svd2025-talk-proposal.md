### SVD'25 Talk proposal

Title: Fault Flow Analysis and Verification with Typestate and Predicate Guards

Abstract:

Faults in hardware and software systems are common and can spread through
programs hard-to-predict ways, raising crucial questions: which parts of a
program are affected and which remain unaffected, and can we verify the adequacy
of fault-handling code in containing these effects? We are developing a
typestate system for fault propagation analysis with selective sanitisation.
This language utilises a static, flow-sensitive type system with guard-tagged
predicates to track data faults from hardware or software failures, combining a
two-point taint lattice with region-parameterised reference types that separate
pointer from payload reliability, and a typestate map joined at control-flow
merge points. It supports higher-order functions whose typing closures prevent
taint from being obscured by abstraction. A three-level type hierarchy (surface,
enriched, qualified) clearly separates user interface, runtime, and analysis
components. The theoretical core consists of a small-step operational semantics
and typing rules, with their executable counterparts in Lean 4 as a definitional
interpreter and a type checker. This foundation allows us to define and prove
formal properties and develop a framework for formal proofs of custom
non-interference properties for any program. This ongoing research at Tufts
University's TuPL group forms part of a DARPA-funded initiative focused on
detecting and recovering from software and hardware faults.

Talk duration: 10–15 minutes
Presenter: Vadim Zaliva <Vadim.Zaliva@tufts.edu>
