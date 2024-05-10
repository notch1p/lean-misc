import Lake
open Lake DSL

package «lean-fp» where
  -- add package configuration options here

lean_lib «LeanFp» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-fp» where
  root := `Main
