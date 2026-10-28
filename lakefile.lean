import Lake
open Lake DSL

package paco where

@[default_target]
lean_lib Paco

lean_lib Tests


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

@[lint_driver]
lean_exe lint where
  root := `Lint
