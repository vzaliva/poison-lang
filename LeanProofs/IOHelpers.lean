import Init.System.IO

namespace LeanProofs

open Classical

/-- Fixed witness used to evaluate `IO` computations when comparing them. -/
noncomputable def defaultWorld : IO.RealWorld :=
  Classical.choice (inferInstance : Nonempty IO.RealWorld)

/-- Evaluate an equality of `IO` computations at the fixed world. -/
@[simp] theorem evalAtDefault_eq {α} {m n : IO α} :
    m = n → m defaultWorld = n defaultWorld := by
  intro h
  simpa using congrArg (fun f => f defaultWorld) h

end LeanProofs
