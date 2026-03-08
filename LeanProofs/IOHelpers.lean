import Init.System.IO

namespace LeanProofs

open Classical

/-- Fixed witness used to evaluate `IO` computations when comparing them.
    In Lean 4.26+, IO uses `Void IO.RealWorld` as the world token type. -/
noncomputable def defaultWorld : Void IO.RealWorld :=
  Void.mk (Classical.choice (inferInstance : Nonempty IO.RealWorld))

/-- Evaluate an equality of `IO` computations at any world. -/
@[simp] theorem evalAtWorld_eq {α} (w : Void IO.RealWorld) {m n : IO α} :
    m = n → m w = n w := by
  intro h; subst h; rfl

/-- Specialization of `evalAtWorld_eq` to the fixed witness. -/
@[simp] theorem evalAtDefault_eq {α} {m n : IO α} :
    m = n → m defaultWorld = n defaultWorld := evalAtWorld_eq defaultWorld

end LeanProofs
