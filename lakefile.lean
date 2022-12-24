import Lake
open Lake DSL

package diploma {
  -- add package configuration options here
}

lean_lib Diploma {
  -- add library configuration options here
}

@[default_target]
lean_exe diploma {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "main"
require mathlib4 from git "https://github.com/leanprover-community/mathlib4" @ "master"
  