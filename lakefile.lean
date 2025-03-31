import Lake
open Lake DSL

package "Computer Algebra System" where
  version := v!"0.1.0"

lean_lib «Computer Algebra System» where
  -- add library configuration options here

@[default_target]
lean_exe "computer algebra system" where
  root := `Main
