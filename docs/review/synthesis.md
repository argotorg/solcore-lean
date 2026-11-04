# Reviewer's guide: Synthesis

`Solcore/Synthesis` holds the generators of the semantic differential tests. A case is a checked
Core program with its reference result, and the source text an emitter prints from it. The external
runner compiles that text with the Rust toolchain and compares what it runs with the reference. The
[umbrella](../../Solcore/Synthesis.lean) gives this reading order in brief.

Two things here need different kinds of review:

- **The generators** are ordinary code. To trust a test, read what a case is, what a profile
  accepts, and how the emitter prints the reference. Nothing here is proved about a profile except
  that its Core program type-checks.
- **`Source/ScalarMeaning`** holds proofs. For fifteen emitters it proves that the text they print
  means what the original Core program computes, under an independent source semantics. It is the
  only part of this area that the kernel check visits.

## Main definitions and theorems

Each entry has its evidence. **README** is "Differential testing". **Emitter note** is
[source emitter meaning preservation](../design/scalar-emitter-meaning.md), and **testing note** is
[semantic differential testing](../design/semantic-differential-testing.md). **Tool** means that
`Tests/SemanticCaseTool.lean` or a stateful tool calls it, and **Root** means that no other
declaration uses it and that it has one of the largest dependency closures of the area.

| Item | Where | Evidence |
| --- | --- | --- |
| The case shape: `caseSchema`, `observe`, `replayCase` | [`Source/Cases`](../../Solcore/Synthesis/Source/Cases.lean) | Testing note, Tool |
| Acceptance rules: `Acceptance`, `InputSelection` | [`Source/Acceptance`](../../Solcore/Synthesis/Source/Acceptance.lean) | Tool |
| The checked fragment: `CheckedWordProgram`, `CheckedWordProgram.wellTyped` | [`Core/Fragment`](../../Solcore/Synthesis/Core/Fragment.lean) | README, testing note |
| Generation and shrinking: `GeneratorRevision`, `Seed`, `Complexity` | [`Core/Generator`](../../Solcore/Synthesis/Core/Generator.lean), [`Core/Seed`](../../Solcore/Synthesis/Core/Seed.lean), [`Core/Shrink`](../../Solcore/Synthesis/Core/Shrink.lean) | Testing note |
| One entry per profile: `generateCases`, `emitCase`, `observe` | the table below | Tool |
| Emitter meaning: `emit_source_meaning` for each emitter | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean), [`Source/ScalarMeaning/LoopTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopTheorems.lean), [`Source/ScalarMeaning/StatefulTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/StatefulTheorems.lean) | README, emitter note, Root |
| Printing and parsing: `parseSource_print` and its variants | [`Source/ScalarMeaning/Grammar`](../../Solcore/Synthesis/Source/ScalarMeaning/Grammar.lean), [`Source/ScalarMeaning/LoopGrammar`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopGrammar.lean), [`Source/ScalarMeaning/StorageGrammar`](../../Solcore/Synthesis/Source/ScalarMeaning/StorageGrammar.lean) | Emitter note, Root |

## Reading order

1. **What a case is.** `Source/Cases`, then `Source/Acceptance`.
2. **What is generated.** `Core/Fragment`, `Core/Seed`, `Core/Generator`, `Core/Shrink`.
3. **What is printed.** `Source/Emitter`.
4. **One profile.** Find it in the table below, and read its file. Each section is one module of
   the base, in dependency order: the Core reference, the renderer, the emitter, the stateful
   execution if there is one, and the cases.
5. **Emitter meaning.** `Source/ScalarMeaning`: the syntax, the grammars, the semantics, and then
   the three theorem files.

## Front

### Cases and generation

| File | Main declarations |
| --- | --- |
| [`Core/Seed`](../../Solcore/Synthesis/Core/Seed.lean) | `Seed`, `Seed.ofNat`, `Seed.draw` |
| [`Core/Fragment`](../../Solcore/Synthesis/Core/Fragment.lean) | `CheckedWordProgram`, `Target`, `Feature`, `acceptsAt` |
| [`Core/Generator`](../../Solcore/Synthesis/Core/Generator.lean) | `GeneratorRevision`, `FeatureMask`, `GeneratedProgram` |
| [`Core/Shrink`](../../Solcore/Synthesis/Core/Shrink.lean) | `Complexity`, `complexity`, `ShrinkCandidate` |
| [`Core/StdDispatch`](../../Solcore/Synthesis/Core/StdDispatch.lean) | `StdDispatch.host`, `StdDispatch.readAt` |
| [`Core/EnumData`](../../Solcore/Synthesis/Core/EnumData.lean) | `Enums.Decl`, `Enums.Ty`, `Enums.Value`, `Enums.Form` |

### Cases and emission

| File | Main declarations |
| --- | --- |
| [`Source/Cases`](../../Solcore/Synthesis/Source/Cases.lean) | `caseSchema`, `corpusSchema`, `observe`, `generateCases`, `replayCase`, `savedMask`, `savedRevision` |
| [`Source/Acceptance`](../../Solcore/Synthesis/Source/Acceptance.lean) | `Acceptance`, `Acceptance.check`, `InputSelection`, `InputSelection.inputs` |
| [`Source/Emitter`](../../Solcore/Synthesis/Source/Emitter.lean) | `EmittedProgram`, `EmitError`, `ScalarRenderer.Rendered` |
| [`Stateful/Sequence`](../../Solcore/Synthesis/Stateful/Sequence.lean) | `Sequence.maxTransactions`, `Sequence.blocks`, `AccountStorage.contractJson`, `StdCalldata` |

### Emitter meaning: specification

These files are the specification of the theorems. They have no reference to Core.

| File | Main declarations |
| --- | --- |
| [`Source/ScalarMeaning/Syntax`](../../Solcore/Synthesis/Source/ScalarMeaning/Syntax.lean) | `Expr`, `Stmt`, `FunctionDecl`, `BinaryOp`, `UnaryOp`, `LocalType` |
| [`Source/ScalarMeaning/Grammar`](../../Solcore/Synthesis/Source/ScalarMeaning/Grammar.lean) | `Token`, `Expr.print`, `parseSource`, `sourceCall` |
| [`Source/ScalarMeaning/LoopGrammar`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopGrammar.lean) | `parseLoopSource`, `loopSourceCall`, `parseGenericSource`, `genericSourceCall` |
| [`Source/ScalarMeaning/StorageGrammar`](../../Solcore/Synthesis/Source/ScalarMeaning/StorageGrammar.lean) | `parseStorageSource`, `storageSourceCall`, `parseRollbackSource`, `rollbackSourceCall`, `parseKeyedSource`, `keyedSourceCall`, `parseLogSource`, `logSourceCall` |
| [`Source/ScalarMeaning/Semantics`](../../Solcore/Synthesis/Source/ScalarMeaning/Semantics.lean) | `Value`, `Frames`, `Context`, `Expr.eval` |
| [`Source/ScalarMeaning/FragmentSemantics`](../../Solcore/Synthesis/Source/ScalarMeaning/FragmentSemantics.lean) | `LoopStmt`, `InfixStmt`, `StorageStmt`, `RollbackStmt`, `KeyedStmt`, `Operand` |
| [`Source/ScalarMeaning/LogSemantics`](../../Solcore/Synthesis/Source/ScalarMeaning/LogSemantics.lean) | `LogStmt`, `LogOutcome` |

## Profiles

A failing run names its profile. This table finds the code. **Tool** is the executable that
generates and replays the profile's cases. Entry points are in the namespace
`Solcore.Synthesis.Source`.

| Profile | Tool | Entry points | File |
| --- | --- | --- | --- |
| `closed-g0` | `semantic-case-tool` | `generateCases`, `replayCase` | [`Source/Cases`](../../Solcore/Synthesis/Source/Cases.lean) |
| `runtime-word` | `semantic-case-tool` | `Input.generateCases`, `Input.emitCase` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-functions` | `semantic-case-tool` | `Function.generateCases`, `Function.emitCase` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-primitives` | `semantic-case-tool` | `Primitive.generateCases`, `Primitive.emitCase` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-mutation` | `semantic-case-tool` | `Mutation.generateCases`, `Mutation.emitCase` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-call-graphs` | `semantic-case-tool` | `CallGraph.generateCases`, `CallGraph.emitCase` | [`Internal/CallGraphs`](../../Solcore/Synthesis/Internal/CallGraphs.lean) |
| `runtime-aggregates` | `semantic-case-tool` | `Aggregate.generateCases`, `Aggregate.emitCase` | [`Internal/Aggregates`](../../Solcore/Synthesis/Internal/Aggregates.lean) |
| `runtime-aggregate-call-graphs` | `semantic-case-tool` | `AggregateCallGraph.generateCases`, `AggregateCallGraph.emitCase` | [`Internal/Aggregates`](../../Solcore/Synthesis/Internal/Aggregates.lean) |
| `runtime-loops` | `semantic-case-tool` | `Loop.generateCases`, `Loop.emitCase` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-nested-loops` | `semantic-case-tool` | `NestedLoop.generateCases`, `NestedLoop.emitCase` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-call-graph-loops` | `semantic-case-tool` | `CallGraphLoop.generateCases`, `CallGraphLoop.emitCase` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-loop-closures` | `semantic-case-tool` | `LoopClosure.generateCases`, `LoopClosure.emitCase` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-recursion` | `semantic-case-tool` | `Recursion.generateCases`, `Recursion.emitCase` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-recursive-loops` | `semantic-case-tool` | `RecursiveLoop.generateCases`, `RecursiveLoop.emitCase` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-closures` | `semantic-case-tool` | `Closure.generateCases`, `Closure.emitCase` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-comptime` | `semantic-case-tool` | `Comptime.generateCases`, `Comptime.emitCase` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-generics` | `semantic-case-tool` | `Generic.generateCases`, `Generic.emitCase` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-modules` | `semantic-case-tool` | `Modules.generateCases`, `Modules.emitCase` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-assembly` | `semantic-case-tool` | `Assembly.generateCases`, `Assembly.emitCase` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `runtime-assembly-memory` | `semantic-case-tool` | `AssemblyMemory.generateCases`, `AssemblyMemory.emitCase` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `runtime-assembly-loops` | `semantic-case-tool` | `AssemblyLoop.generateCases`, `AssemblyLoop.emitCase` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `runtime-enums` | `semantic-case-tool` | `Enums.generateCases`, `Enums.emitCase` | [`Internal/Enums`](../../Solcore/Synthesis/Internal/Enums.lean) |
| `runtime-traits` | `semantic-case-tool` | `Traits.generateCases`, `Traits.emitCase` | [`Internal/Traits`](../../Solcore/Synthesis/Internal/Traits.lean) |
| `runtime-trait-hierarchies` | `semantic-case-tool` | `Hierarchies.generateCases`, `Hierarchies.emitCase` | [`Internal/Traits`](../../Solcore/Synthesis/Internal/Traits.lean) |
| `runtime-memory-values` | `semantic-case-tool` | `MemoryValues.generateCases`, `MemoryValues.emitCase` | [`Internal/MemoryValues`](../../Solcore/Synthesis/Internal/MemoryValues.lean) |
| `runtime-memory-calls` | `semantic-case-tool` | `MemoryCalls.generateCases`, `MemoryCalls.emitCase` | [`Internal/MemoryCalls`](../../Solcore/Synthesis/Internal/MemoryCalls.lean) |
| `runtime-revert-data` | `semantic-case-tool` | `RevertData.generateCases`, `RevertData.emitCase` | [`Internal/RevertData`](../../Solcore/Synthesis/Internal/RevertData.lean) |
| `runtime-halts` | `semantic-case-tool` | `Halts.generateCases`, `Halts.emitCase` | [`Internal/RevertData`](../../Solcore/Synthesis/Internal/RevertData.lean) |
| `runtime-checked-arithmetic` | `semantic-case-tool` | `CheckedArithmetic.generateCases`, `CheckedArithmetic.emitCase` | [`Internal/Integers`](../../Solcore/Synthesis/Internal/Integers.lean) |
| `runtime-shifts` | `semantic-case-tool` | `Shifts.generateCases`, `Shifts.emitCase` | [`Internal/Integers`](../../Solcore/Synthesis/Internal/Integers.lean) |
| `runtime-memory-arrays` | `semantic-case-tool` | `MemoryArrays.generateCases`, `MemoryArrays.emitCase` | [`Internal/Arrays`](../../Solcore/Synthesis/Internal/Arrays.lean) |
| `runtime-array-abi` | `semantic-case-tool` | `ArrayAbi.generateCases`, `ArrayAbi.emitCase` | [`Internal/Arrays`](../../Solcore/Synthesis/Internal/Arrays.lean) |
| `stateful-storage` | `semantic-storage-tool` | `Storage.generateCases`, `Storage.emitCase`, `Storage.observe` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-storage-rollback` | `semantic-storage-rollback-tool` | `StorageRollback.generateCases`, `StorageRollback.emitCase`, `StorageRollback.observe` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-keyed-storage` | `semantic-keyed-storage-tool` | `KeyedStorage.generateCases`, `KeyedStorage.emitCase`, `KeyedStorage.observe` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-mapping` | `semantic-mapping-tool` | `StorageMapping.generateCases`, `StorageMapping.emitCase`, `StorageMapping.observe` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-ledger` | `semantic-ledger-tool` | `StorageLedger.generateCases`, `StorageLedger.emitCase`, `StorageLedger.observe` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-storage-loops` | `semantic-storage-loop-tool` | `StorageLoop.generateCases`, `StorageLoop.emitCase`, `StorageLoop.observe` | [`Internal/StorageLoops`](../../Solcore/Synthesis/Internal/StorageLoops.lean) |
| `stateful-keccak-loops` | `semantic-keccak-loop-tool` | `KeccakLoop.generateCases`, `KeccakLoop.emitCase`, `KeccakLoop.observe` | [`Internal/StorageLoops`](../../Solcore/Synthesis/Internal/StorageLoops.lean) |
| `stateful-assembly-storage-loops` | `semantic-assembly-storage-loop-tool` | `AssemblyStorageLoop.generateCases`, `AssemblyStorageLoop.emitCase`, `AssemblyStorageLoop.observe` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `stateful-assembly-keccak-loops` | `semantic-assembly-keccak-loop-tool` | `AssemblyKeccakLoop.generateCases`, `AssemblyKeccakLoop.emitCase`, `AssemblyKeccakLoop.observe` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `stateful-adt-storage` | `semantic-adt-storage-tool` | `AdtStorage.generateCases`, `AdtStorage.emitCase`, `AdtStorage.observe` | [`Internal/AdtStorage`](../../Solcore/Synthesis/Internal/AdtStorage.lean) |
| `stateful-logs` | `semantic-log-tool` | `EventLog.generateCases`, `EventLog.emitCase`, `EventLog.observe` | [`Internal/AdtStorage`](../../Solcore/Synthesis/Internal/AdtStorage.lean) |
| `stateful-calls` | `semantic-call-tool` | `NestedCall.generateCases`, `NestedCall.emitCase`, `NestedCall.observe` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-call-value` | `semantic-call-value-tool` | `CallValue.generateCases`, `CallValue.emitCase`, `CallValue.observe` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-forwarded-value` | `semantic-forward-tool` | `ForwardedCall.generateCases`, `ForwardedCall.emitCase`, `ForwardedCall.observe` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-methods` | `semantic-methods-tool` | `Methods.generateCases`, `Methods.emitCase`, `Methods.observe` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-call-returns` | `semantic-call-return-tool` | `CallReturn.generateCases`, `CallReturn.emitCase`, `CallReturn.observe` | [`Internal/CallReturns`](../../Solcore/Synthesis/Internal/CallReturns.lean) |
| `stateful-call-sequences` | `semantic-call-sequence-tool` | `CallSequence.generateCases`, `CallSequence.emitCase`, `CallSequence.observe` | [`Internal/CallReturns`](../../Solcore/Synthesis/Internal/CallReturns.lean) |
| `stateful-call-branches` | `semantic-call-branch-tool` | `CallBranch.generateCases`, `CallBranch.emitCase`, `CallBranch.observe` | [`Internal/CallReturns`](../../Solcore/Synthesis/Internal/CallReturns.lean) |
| `stateful-constructor-arguments` | `semantic-constructor-argument-tool` | `ConstructorArguments.generateCases`, `ConstructorArguments.emitCase`, `ConstructorArguments.observe` | [`Internal/ConstructorArguments`](../../Solcore/Synthesis/Internal/ConstructorArguments.lean) |
| `stateful-bytes-returns` | `semantic-bytes-return-tool` | `BytesReturn.generateCases`, `BytesReturn.emitCase`, `BytesReturn.observe` | [`Internal/AbiReturns`](../../Solcore/Synthesis/Internal/AbiReturns.lean) |
| `stateful-tuple-returns` | `semantic-tuple-return-tool` | `TupleReturn.generateCases`, `TupleReturn.emitCase`, `TupleReturn.observe` | [`Internal/AbiReturns`](../../Solcore/Synthesis/Internal/AbiReturns.lean) |
| `stateful-array-returns` | `semantic-array-return-tool` | `ArrayReturn.generateCases`, `ArrayReturn.emitCase`, `ArrayReturn.observe` | [`Internal/AbiReturns`](../../Solcore/Synthesis/Internal/AbiReturns.lean) |
| `stateful-enum-returns` | `semantic-enum-return-tool` | `EnumReturn.generateCases`, `EnumReturn.emitCase`, `EnumReturn.observe` | [`Internal/EnumAbi`](../../Solcore/Synthesis/Internal/EnumAbi.lean) |
| `stateful-enum-arguments` | `semantic-enum-argument-tool` | `EnumArgument.generateCases`, `EnumArgument.emitCase`, `EnumArgument.observe` | [`Internal/EnumAbi`](../../Solcore/Synthesis/Internal/EnumAbi.lean) |
| `stateful-enum-array-arguments` | `semantic-enum-array-tool` | `EnumArray.generateCases`, `EnumArray.emitCase`, `EnumArray.observe` | [`Internal/EnumAbi`](../../Solcore/Synthesis/Internal/EnumAbi.lean) |
| `stateful-dynamic-array` | `semantic-dynamic-array-tool` | `DynamicArray.generateCases`, `DynamicArray.emitCase`, `DynamicArray.observe` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-bytes` | `semantic-bytes-tool` | `DynamicBytes.generateCases`, `DynamicBytes.emitCase`, `DynamicBytes.observe` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-long-bytes` | `semantic-long-bytes-tool` | `LongBytes.generateCases`, `LongBytes.emitCase`, `LongBytes.observe` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-nested-array` | `semantic-nested-array-tool` | `NestedArray.generateCases`, `NestedArray.emitCase`, `NestedArray.observe` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-malformed-calldata` | `semantic-malformed-calldata-tool` | `MalformedCalldata.generateCases`, `MalformedCalldata.emitCase`, `MalformedCalldata.observe` | [`Internal/Malformed`](../../Solcore/Synthesis/Internal/Malformed.lean) |
| `stateful-malformed-bytes` | `semantic-malformed-bytes-tool` | `MalformedBytes.generateCases`, `MalformedBytes.emitCase`, `MalformedBytes.observe` | [`Internal/Malformed`](../../Solcore/Synthesis/Internal/Malformed.lean) |
| `stateful-malformed-nested-array` | `semantic-malformed-nested-array-tool` | `MalformedNestedArray.generateCases`, `MalformedNestedArray.emitCase`, `MalformedNestedArray.observe` | [`Internal/Malformed`](../../Solcore/Synthesis/Internal/Malformed.lean) |

`scripts/SEMANTIC_DIFFERENTIAL.md` says what each profile compares, and which paths it runs on.

## Main theorems

The [emitter note](../design/scalar-emitter-meaning.md) states each one, and its limits. Each
`emit_preserves_meaning` is the same result with the parsed source file exposed. In the namespace
`Solcore.Synthesis.Source.ScalarMeaning`:

| Profile | Theorem | File |
| --- | --- | --- |
| `closed-g0` | `emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-word` | `Input.emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-functions` | `Function.emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-primitives` | `Primitive.emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-call-graphs` | `CallGraph.emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-mutation` | `Mutation.emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-aggregates` | `Aggregate.emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-aggregate-call-graphs` | `AggregateCallGraph.emit_source_meaning` | [`Source/ScalarMeaning/PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean) |
| `runtime-call-graph-loops` | `CallGraphLoop.emit_source_meaning` | [`Source/ScalarMeaning/LoopTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopTheorems.lean) |
| `runtime-loops` | `Loop.emit_source_meaning` | [`Source/ScalarMeaning/LoopTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopTheorems.lean) |
| `runtime-generics` | `Generic.emit_source_meaning` | [`Source/ScalarMeaning/LoopTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopTheorems.lean) |
| `stateful-storage` | `Storage.emit_source_meaning` | [`Source/ScalarMeaning/StatefulTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/StatefulTheorems.lean) |
| `stateful-storage-rollback` | `StorageRollback.emit_source_meaning` | [`Source/ScalarMeaning/StatefulTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/StatefulTheorems.lean) |
| `stateful-keyed-storage` | `KeyedStorage.emit_source_meaning` | [`Source/ScalarMeaning/StatefulTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/StatefulTheorems.lean) |
| `stateful-logs` | `EventLog.emit_source_meaning` | [`Source/ScalarMeaning/StatefulTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/StatefulTheorems.lean) |

No other profile has a theorem. The grammars add `parseSource_print`, `parseLoopSource_print`,
`parseGenericSource_print`, `parseStorageSource_print`, `parseRollbackSource_print`,
`parseKeyedSource_print` and `parseLogSource_print`: the printed text of a file parses back to that
file.

Each pure theorem is about a closed run of `Core.Program`. The stateful ones are about one
top-level transaction on a world in which the contract is installed, so they apply to each
transaction of a history in turn.

## Internal

Profiles are in `Internal/`, one file per family, and the table above lists them.

| File | Topic |
| --- | --- |
| [`Internal/AbiReturns`](../../Solcore/Synthesis/Internal/AbiReturns.lean) | The profiles `stateful-bytes-returns`, `stateful-tuple-returns` and `stateful-array-returns`. |
| [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) | The profiles `stateful-dynamic-array`, `stateful-bytes`, `stateful-long-bytes` and `stateful-nested-array`. |
| [`Internal/AdtStorage`](../../Solcore/Synthesis/Internal/AdtStorage.lean) | The profiles `stateful-adt-storage` and `stateful-logs`. |
| [`Internal/Aggregates`](../../Solcore/Synthesis/Internal/Aggregates.lean) | The profiles `runtime-aggregates` and `runtime-aggregate-call-graphs`. |
| [`Internal/Arrays`](../../Solcore/Synthesis/Internal/Arrays.lean) | The profiles `runtime-memory-arrays` and `runtime-array-abi`. |
| [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) | The profiles `runtime-assembly`, `runtime-assembly-memory`, `runtime-assembly-loops`, `stateful-assembly-storage-loops` and `stateful-assembly-keccak-loops`. |
| [`Internal/CallGraphs`](../../Solcore/Synthesis/Internal/CallGraphs.lean) | The profile `runtime-call-graphs`: generator, renderer, emitter and cases. |
| [`Internal/CallReturns`](../../Solcore/Synthesis/Internal/CallReturns.lean) | The profiles `stateful-call-returns`, `stateful-call-sequences` and `stateful-call-branches`. |
| [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) | The profiles `stateful-calls`, `stateful-call-value`, `stateful-forwarded-value` and `stateful-methods`. |
| [`Internal/ConstructorArguments`](../../Solcore/Synthesis/Internal/ConstructorArguments.lean) | The profile `stateful-constructor-arguments`. |
| [`Internal/EnumAbi`](../../Solcore/Synthesis/Internal/EnumAbi.lean) | The profiles `stateful-enum-returns`, `stateful-enum-arguments` and `stateful-enum-array-arguments`. |
| [`Internal/Enums`](../../Solcore/Synthesis/Internal/Enums.lean) | The profile `runtime-enums`: views over enum values, reductions, emitter and cases. |
| [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) | The profiles `runtime-word`, `runtime-functions`, `runtime-primitives` and `runtime-mutation`: Core references, renderers, emitters and cases. |
| [`Internal/Integers`](../../Solcore/Synthesis/Internal/Integers.lean) | The profiles `runtime-checked-arithmetic` and `runtime-shifts`. |
| [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) | The profiles `runtime-closures`, `runtime-comptime`, `runtime-generics` and `runtime-modules`. |
| [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) | The profiles `runtime-loops`, `runtime-nested-loops`, `runtime-call-graph-loops`, `runtime-loop-closures`, `runtime-recursion` and `runtime-recursive-loops`. |
| [`Internal/Malformed`](../../Solcore/Synthesis/Internal/Malformed.lean) | The profiles `stateful-malformed-calldata`, `stateful-malformed-bytes` and `stateful-malformed-nested-array`. |
| [`Internal/MemoryCalls`](../../Solcore/Synthesis/Internal/MemoryCalls.lean) | The profile `runtime-memory-calls`. |
| [`Internal/MemoryValues`](../../Solcore/Synthesis/Internal/MemoryValues.lean) | The profile `runtime-memory-values`. |
| [`Internal/RevertData`](../../Solcore/Synthesis/Internal/RevertData.lean) | The profiles `runtime-revert-data` and `runtime-halts`. |
| [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) | The profiles `stateful-storage`, `stateful-storage-rollback`, `stateful-keyed-storage`, `stateful-mapping` and `stateful-ledger`. |
| [`Internal/StorageLoops`](../../Solcore/Synthesis/Internal/StorageLoops.lean) | The profiles `stateful-storage-loops` and `stateful-keccak-loops`. |
| [`Internal/Traits`](../../Solcore/Synthesis/Internal/Traits.lean) | The profiles `runtime-traits` and `runtime-trait-hierarchies`. |

The proofs behind the emitter theorems are in `Source/ScalarMeaning/Internal/`.

| File | Topic |
| --- | --- |
| [`Source/ScalarMeaning/Internal/Aggregates`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/Aggregates.lean) | The aggregate and aggregate call-graph renderers. |
| [`Source/ScalarMeaning/Internal/CallGraphs`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/CallGraphs.lean) | The raw primitive and call-graph renderers, and agreement of Core Word operations with EVM operations. |
| [`Source/ScalarMeaning/Internal/Mutation`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/Mutation.lean) | The private-mutation renderer, with its store-aware invariant. |
| [`Source/ScalarMeaning/Internal/Renderer`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/Renderer.lean) | Induction over the actual scalar renderer, and simulation lemmas generic over a renderer of its shape. |

## What a reviewer should know

- **The kernel check visits only `Source/ScalarMeaning`.** Every file of that directory, and nothing
  else in this area, is held to the policy of `scripts/check-kernel.mjs`. No file outside the
  directory joined it, and none of its files left.
- **Core typing is not meaning.** `CheckedWordProgram.wellTyped` says that a program type-checks. It
  says nothing about what an emitter prints. That is what the theorems above are for, and they cover
  fifteen emitters of the sixty-four profiles.
- **The emitted text is the test input.** Changing a renderer's output changes every saved corpus
  of its profile. The corpus validators in `scripts/` catch that.
- **The grammars stay apart from the semantics.** Each fragment's `*Semantics` derives `Repr`, and
  the matcher of that instance has the same shape as the matcher of `tokens` in its text module. In
  one file Lean reuses the first, and `tokens.eq_i` would take its binder names from `Repr`.
