import Init.System.IO

namespace LeanProofs

open Classical

/-- Fixed witness used to evaluate `IO` computations when comparing them. -/
noncomputable def defaultWorld : IO.RealWorld :=
  Classical.choice (inferInstance : Nonempty IO.RealWorld)

/-- Evaluate an equality of `IO` computations at any world. -/
@[simp] theorem evalAtWorld_eq {α} (w : IO.RealWorld) {m n : IO α} :
    m = n → m w = n w := by
  intro h
  simpa using congrArg (fun f => f w) h

/-- Specialization of `evalAtWorld_eq` to the fixed witness. -/
@[simp] theorem evalAtDefault_eq {α} {m n : IO α} :
    m = n → m defaultWorld = n defaultWorld :=
  evalAtWorld_eq defaultWorld

end LeanProofs
