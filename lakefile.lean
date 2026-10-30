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

lean_exe semanticMalformedCalldataTool where
  root := `Tests.SemanticMalformedCalldataTool
  exeName := "semantic-malformed-calldata-tool"

lean_exe semanticMalformedNestedArrayTool where
  root := `Tests.SemanticMalformedNestedArrayTool
  exeName := "semantic-malformed-nested-array-tool"

lean_exe semanticMalformedBytesTool where
  root := `Tests.SemanticMalformedBytesTool
  exeName := "semantic-malformed-bytes-tool"

lean_exe semanticMethodsTool where
  root := `Tests.SemanticMethodsTool
  exeName := "semantic-methods-tool"

lean_exe semanticStorageLoopTool where
  root := `Tests.SemanticStorageLoopTool
  exeName := "semantic-storage-loop-tool"

lean_exe semanticKeccakLoopTool where
  root := `Tests.SemanticKeccakLoopTool
  exeName := "semantic-keccak-loop-tool"

lean_exe semanticTupleReturnTool where
  root := `Tests.SemanticTupleReturnTool
  exeName := "semantic-tuple-return-tool"

lean_exe semanticAssemblyStorageLoopTool where
  root := `Tests.SemanticAssemblyStorageLoopTool
  exeName := "semantic-assembly-storage-loop-tool"

lean_exe semanticAssemblyKeccakLoopTool where
  root := `Tests.SemanticAssemblyKeccakLoopTool
  exeName := "semantic-assembly-keccak-loop-tool"

lean_exe semanticBytesReturnTool where
  root := `Tests.SemanticBytesReturnTool
  exeName := "semantic-bytes-return-tool"

lean_exe semanticAdtStorageTool where
  root := `Tests.SemanticAdtStorageTool
  exeName := "semantic-adt-storage-tool"

lean_exe semanticEnumReturnTool where
  root := `Tests.SemanticEnumReturnTool
  exeName := "semantic-enum-return-tool"

lean_exe semanticEnumArgumentTool where
  root := `Tests.SemanticEnumArgumentTool
  exeName := "semantic-enum-argument-tool"

lean_exe semanticEnumArrayTool where
  root := `Tests.SemanticEnumArrayTool
  exeName := "semantic-enum-array-tool"

lean_exe semanticArrayReturnTool where
  root := `Tests.SemanticArrayReturnTool
  exeName := "semantic-array-return-tool"

lean_exe semanticConstructorArgumentTool where
  root := `Tests.SemanticConstructorArgumentTool
  exeName := "semantic-constructor-argument-tool"

lean_exe semanticCallReturnTool where
  root := `Tests.SemanticCallReturnTool
  exeName := "semantic-call-return-tool"

lean_exe rustHullCallReturnScenario where
  root := `Tests.RustHullCallReturnScenarioRun
  exeName := "rust-hull-call-return-scenario"

lean_exe semanticEventLogTool where
  root := `Tests.SemanticEventLogTool
  exeName := "semantic-log-tool"

lean_exe semanticCallValueTool where
  root := `Tests.SemanticCallValueTool
  exeName := "semantic-call-value-tool"

lean_exe rustHullValueScenario where
  root := `Tests.RustHullValueScenarioRun
  exeName := "rust-hull-value-scenario"

lean_exe semanticBytesTool where
  root := `Tests.SemanticBytesTool
  exeName := "semantic-bytes-tool"

lean_exe semanticForwardTool where
  root := `Tests.SemanticForwardTool
  exeName := "semantic-forward-tool"

lean_exe rustHullForwardScenario where
  root := `Tests.RustHullForwardScenarioRun
  exeName := "rust-hull-forward-scenario"

lean_exe semanticMappingTool where
  root := `Tests.SemanticMappingTool
  exeName := "semantic-mapping-tool"

lean_exe semanticLedgerTool where
  root := `Tests.SemanticLedgerTool
  exeName := "semantic-ledger-tool"

lean_exe rustHullLedgerScenario where
  root := `Tests.RustHullLedgerScenarioRun
  exeName := "rust-hull-ledger-scenario"

lean_exe semanticLongBytesTool where
  root := `Tests.SemanticLongBytesTool
  exeName := "semantic-long-bytes-tool"

lean_exe semanticNestedArrayTool where
  root := `Tests.SemanticNestedArrayTool
  exeName := "semantic-nested-array-tool"
