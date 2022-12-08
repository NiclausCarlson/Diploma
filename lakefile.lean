import Lake
open Lake DSL

package diploma {
  -- add package configuration options here
}

lean_lib Diploma {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe diploma {
  root := `Main
}
