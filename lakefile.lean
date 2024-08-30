import Lake
open Lake DSL

package «lean-fp» {
  -- moreLinkArgs := #[
  --   "-L./.lake/packages/LeanCopilot/.lake/build/lib",
  --   "-lctranslate2"
  -- ]
}

lean_lib «LeanFp» where
  -- add library configuration options here

@[default_target]
lean_exe «lean-fp» where
  root := `Main

-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.5.0"
