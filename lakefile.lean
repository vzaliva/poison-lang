import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

package «lean-poison» where
  -- Default targets are set via `@[default_target]` on declarations below
  restoreAllArtifacts := true

@[default_target]
lean_lib LeanPoison where
  -- Compile all modules under the `LeanPoison` namespace
  globs := #[.submodules `LeanPoison]

@[default_target]
lean_lib LeanProofs where
  -- Compile all modules under the `LeanProofs` namespace
  globs := #[.submodules `LeanProofs]

@[default_target]
lean_exe «poison-interpreter» where
  root := `Main
