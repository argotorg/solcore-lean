import Lake

open Lake DSL

package «solcore-lean» where
  leanOptions := #[
    ⟨`warningAsError, true⟩
  ]

@[default_target]
lean_lib Solcore where
  globs := `Solcore.*

@[test_driver]
lean_exe solcoreTests where
  root := `Tests.Main
  exeName := "solcore-tests"
