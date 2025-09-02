import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

package «lean-poison» where
  -- Default targets are set via `@[default_target]` on declarations below

@[default_target]
lean_lib LeanPoison where
  -- Compile all modules under the `LeanPoison` namespace
  globs := #[.submodules `LeanPoison]

lean_lib LeanProofs where
  -- Compile all modules under the `LeanProofs` namespace (not a default target)
  globs := #[.submodules `LeanProofs]

@[default_target]
lean_exe «poison-interpreter» where
  root := `Main
