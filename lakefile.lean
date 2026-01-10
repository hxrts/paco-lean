import Lake
open Lake DSL

package paco {
}

@[default_target]
lean_lib Paco

lean_lib Tests

lean_lib Standalone

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.26.0"
