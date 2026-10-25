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

lean_exe semanticCaseTool where
  root := `Tests.SemanticCaseTool
  exeName := "semantic-case-tool"

lean_exe semanticStorageTool where
  root := `Tests.SemanticStorageTool
  exeName := "semantic-storage-tool"

lean_exe rustHullStorageScenario where
  root := `Tests.RustHullStorageScenarioRun
  exeName := "rust-hull-storage-scenario"

lean_exe rustHullScenario where
  root := `Tests.RustHullScenarioRun
  exeName := "rust-hull-scenario"

lean_exe rustHullContract where
  root := `Tests.RustHullContractRun
  exeName := "rust-hull-contract"
