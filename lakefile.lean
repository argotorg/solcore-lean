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

lean_exe semanticStorageRollbackTool where
  root := `Tests.SemanticStorageRollbackTool
  exeName := "semantic-storage-rollback-tool"

lean_exe semanticCallTool where
  root := `Tests.SemanticCallTool
  exeName := "semantic-call-tool"

lean_exe rustHullCallScenario where
  root := `Tests.RustHullCallScenarioRun
  exeName := "rust-hull-call-scenario"

lean_exe rustHullStorageScenario where
  root := `Tests.RustHullStorageScenarioRun
  exeName := "rust-hull-storage-scenario"

lean_exe rustHullScenario where
  root := `Tests.RustHullScenarioRun
  exeName := "rust-hull-scenario"

lean_exe rustHullContract where
  root := `Tests.RustHullContractRun
  exeName := "rust-hull-contract"

lean_exe semanticKeyedStorageTool where
  root := `Tests.SemanticKeyedStorageTool
  exeName := "semantic-keyed-storage-tool"

lean_exe rustHullKeyedStorageScenario where
  root := `Tests.RustHullKeyedStorageScenarioRun
  exeName := "rust-hull-keyed-storage-scenario"

lean_exe semanticDynamicArrayTool where
  root := `Tests.SemanticDynamicArrayTool
  exeName := "semantic-dynamic-array-tool"

lean_exe semanticEventLogTool where
  root := `Tests.SemanticEventLogTool
  exeName := "semantic-log-tool"
