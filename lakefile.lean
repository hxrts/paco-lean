import Lake
open Lake DSL

package paco {
}

@[default_target]
lean_lib Paco

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"master"
