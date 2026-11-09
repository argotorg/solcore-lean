# Synthesis

`Solcore/Synthesis` generates the programs of the differential tests against solcore-rs. A case
is a checked Core program, the original Core reference, with the Solcore source text that an
emitter prints from it. The runners in `scripts/` compile that text with the Rust toolchain, run
it, and compare the result with the reference; [Differential testing](differential-testing.md)
explains the comparison.

- **Generators** draw checked programs or plans from a seed, and reduce them.
- **Emitters** print a program or plan as a contract.
- **Profiles** pair a generator with an emitter and a case format; a stateful profile adds a
  transaction model. A failing run names its profile.
- **Emitter meaning** (`Source/ScalarMeaning/`) proves, for some emitters, that the printed text
  means what the Core program computes, under an independent source semantics.

The area builds on Core (the checker, the Wire codec, the machine) and on ContractRuntime (the
top-level transaction). No other area imports it: its users are the case tools in `Tests/`, the
tests in `Solcore/Test/Synthesis/`, and the Python runners, which read the JSON the tools print. The
[umbrella](../../Solcore/Synthesis.lean) gives the reading order.

## Where things are

### Front

| File | Holds |
| --- | --- |
| [`Core/Seed`](../../Solcore/Synthesis/Core/Seed.lean) | `Seed` (`lcg64-v1`), `Seed.ofNat`, `Seed.draw`, `Seed.choose`: the stream every generator draws from |
| [`Core/Fragment`](../../Solcore/Synthesis/Core/Fragment.lean) | The G0 fragment: `CheckedWordProgram`, `CheckedWordProgram.wellTyped`, `Target`, `Feature`, `acceptsAt` |
| [`Core/Generator`](../../Solcore/Synthesis/Core/Generator.lean) | The G0 generator: `GeneratorRevision` (`v1` to `v4`), `FeatureMask`, `GeneratedProgram` |
| [`Core/Shrink`](../../Solcore/Synthesis/Core/Shrink.lean) | G0 reductions: `Complexity`, `complexity`, `ShrinkCandidate` |
| [`Core/StdDispatch`](../../Solcore/Synthesis/Core/StdDispatch.lean) | The Core model of std's dispatcher behind the stateful contracts: `StdDispatch.host`, `StdDispatch.readAt` |
| [`Core/EnumData`](../../Solcore/Synthesis/Core/EnumData.lean) | User enums as plans (`Enums.Decl`, `Enums.Ty`, `Enums.Value`, `Enums.Form`), and the draw helpers `Enums.Gen`, `Enums.draw`, `Enums.drawWeighted` that newer plans use |
| [`Source/Cases`](../../Solcore/Synthesis/Source/Cases.lean) | The `closed-g0` case and corpus: `caseSchema`, `corpusSchema`, `observe`, `generateCases`, `replayCase`, `savedMask`, `savedRevision` |
| [`Source/Acceptance`](../../Solcore/Synthesis/Source/Acceptance.lean) | `Acceptance` (the filter `exclude-boundary-identity-v1`) and `InputSelection` (`seeded-inputs-v1/splitmix64`) |
| [`Source/Emitter`](../../Solcore/Synthesis/Source/Emitter.lean) | `EmittedProgram`, which most emitters return, `EmitError`, and `ScalarRenderer` with the closed G0 `emit` |
| [`Stateful/Sequence`](../../Solcore/Synthesis/Stateful/Sequence.lean) | `Sequence.maxTransactions`, `Sequence.blocks`, `AccountStorage.contractJson`, and the section `StdCalldata`, a byte-level model of std's calldata decoder for the malformed profiles |

### Emitter meaning

The syntax, semantics and grammar files are the specification and have no reference to Core; the
theorem files connect them to the emitters and to Core.

| File | Holds |
| --- | --- |
| [`Source/ScalarMeaning/Syntax`](../../Solcore/Synthesis/Source/ScalarMeaning/Syntax.lean) | `Expr`, `Stmt`, `FunctionDecl`, `BinaryOp`, `UnaryOp`, `LocalType` |
| [`Source/ScalarMeaning/Semantics`](../../Solcore/Synthesis/Source/ScalarMeaning/Semantics.lean) | `Value`, `Frames`, `Context`, `Expr.eval` |
| [`Source/ScalarMeaning/FragmentSemantics`](../../Solcore/Synthesis/Source/ScalarMeaning/FragmentSemantics.lean) | Loop, generic, storage, rollback and keyed programs: `LoopStmt`, `InfixStmt`, `StorageStmt`, `RollbackStmt`, `KeyedStmt`, `Operand` |
| [`Source/ScalarMeaning/LogSemantics`](../../Solcore/Synthesis/Source/ScalarMeaning/LogSemantics.lean) | Log programs: `LogStmt`, `LogOutcome` |
| [`Source/ScalarMeaning/Grammar`](../../Solcore/Synthesis/Source/ScalarMeaning/Grammar.lean) | `Token`, `Expr.print`, `parseSource`, `sourceCall`, and the round trip `parseSource_print`: printed text parses back to its file |
| [`Source/ScalarMeaning/LoopGrammar`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopGrammar.lean) | `parseLoopSource`, `loopSourceCall`, `parseGenericSource`, `genericSourceCall`; `parseLoopSource_print`, `parseGenericSource_print` |
| [`Source/ScalarMeaning/StorageGrammar`](../../Solcore/Synthesis/Source/ScalarMeaning/StorageGrammar.lean) | The storage, rollback, keyed and log grammars and calls; `parseStorageSource_print`, `parseRollbackSource_print`, `parseKeyedSource_print`, `parseLogSource_print` |
| [`PureTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/PureTheorems.lean), [`LoopTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/LoopTheorems.lean), [`StatefulTheorems`](../../Solcore/Synthesis/Source/ScalarMeaning/StatefulTheorems.lean) | The `emit_source_meaning` theorems, by kind of emitter |
| `Internal/` [`Renderer`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/Renderer.lean), [`CallGraphs`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/CallGraphs.lean), [`Mutation`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/Mutation.lean), [`Aggregates`](../../Solcore/Synthesis/Source/ScalarMeaning/Internal/Aggregates.lean) | The proofs, one file per renderer, each with its induction: `render_spec` (over `ScalarRenderer`), `primitive_render_spec` and `callGraph_render_spec` (with Core Word operations against EVM ones), `mutation_render_spec`, `aggregate_render_spec` and `aggregateCallGraph_render_spec` |

### Profiles

`Internal/` has one file per family of profiles; its module doc names them. A file holds its
sections in dependency order: the plans in `Solcore.Synthesis.Core.*`, each with its Core
reference, generation and reductions; the emitters; for stateful profiles the transaction models in
`Solcore.Synthesis.Stateful.*Execution`; and the cases. A profile's cases, and usually its emitter,
are in its namespace below, under `Solcore.Synthesis.Source`. It holds `generateCases` and
`emitCase`, and for a stateful profile also `observe`.

The pure profiles share `semantic-case-tool`. Each has a generate command and a matching `-emit`
command; `observe`, `replay` and `shrink` choose the profile by the case's schema.

| Profile | Namespace | Command | File |
| --- | --- | --- | --- |
| `closed-g0` | (root) | `generate` | [`Source/Cases`](../../Solcore/Synthesis/Source/Cases.lean) |
| `runtime-word` | `Input` | `input-generate` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-functions` | `Function` | `function-generate` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-primitives` | `Primitive` | `primitive-generate` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-mutation` | `Mutation` | `mutation-generate` | [`Internal/Functions`](../../Solcore/Synthesis/Internal/Functions.lean) |
| `runtime-call-graphs` | `CallGraph` | `call-graph-generate` | [`Internal/CallGraphs`](../../Solcore/Synthesis/Internal/CallGraphs.lean) |
| `runtime-aggregates` | `Aggregate` | `aggregate-generate` | [`Internal/Aggregates`](../../Solcore/Synthesis/Internal/Aggregates.lean) |
| `runtime-aggregate-call-graphs` | `AggregateCallGraph` | `aggregate-call-graph-generate` | [`Internal/Aggregates`](../../Solcore/Synthesis/Internal/Aggregates.lean) |
| `runtime-loops` | `Loop` | `loop-generate` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-nested-loops` | `NestedLoop` | `nested-loop-generate` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-call-graph-loops` | `CallGraphLoop` | `call-graph-loop-generate` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-loop-closures` | `LoopClosure` | `loop-closure-generate` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-recursion` | `Recursion` | `recursion-generate` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-recursive-loops` | `RecursiveLoop` | `recursive-loop-generate` | [`Internal/Loops`](../../Solcore/Synthesis/Internal/Loops.lean) |
| `runtime-closures` | `Closure` | `closure-generate` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-comptime` | `Comptime` | `comptime-generate` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-generics` | `Generic` | `generic-generate` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-modules` | `Modules` | `module-generate` | [`Internal/LanguageFeatures`](../../Solcore/Synthesis/Internal/LanguageFeatures.lean) |
| `runtime-assembly` | `Assembly` | `assembly-generate` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `runtime-assembly-memory` | `AssemblyMemory` | `assembly-memory-generate` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `runtime-assembly-loops` | `AssemblyLoop` | `assembly-loop-generate` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `runtime-enums` | `Enums` | `enum-generate` | [`Internal/Enums`](../../Solcore/Synthesis/Internal/Enums.lean) |
| `runtime-traits` | `Traits` | `trait-generate` | [`Internal/Traits`](../../Solcore/Synthesis/Internal/Traits.lean) |
| `runtime-trait-hierarchies` | `Hierarchies` | `hierarchy-generate` | [`Internal/Traits`](../../Solcore/Synthesis/Internal/Traits.lean) |
| `runtime-memory-values` | `MemoryValues` | `memory-values-generate` | [`Internal/MemoryValues`](../../Solcore/Synthesis/Internal/MemoryValues.lean) |
| `runtime-memory-calls` | `MemoryCalls` | `memory-calls-generate` | [`Internal/MemoryCalls`](../../Solcore/Synthesis/Internal/MemoryCalls.lean) |
| `runtime-revert-data` | `RevertData` | `revert-data-generate` | [`Internal/RevertData`](../../Solcore/Synthesis/Internal/RevertData.lean) |
| `runtime-halts` | `Halts` | `halt-generate` | [`Internal/RevertData`](../../Solcore/Synthesis/Internal/RevertData.lean) |
| `runtime-checked-arithmetic` | `CheckedArithmetic` | `checked-arithmetic-generate` | [`Internal/Integers`](../../Solcore/Synthesis/Internal/Integers.lean) |
| `runtime-shifts` | `Shifts` | `shift-generate` | [`Internal/Integers`](../../Solcore/Synthesis/Internal/Integers.lean) |
| `runtime-memory-arrays` | `MemoryArrays` | `memory-arrays-generate` | [`Internal/Arrays`](../../Solcore/Synthesis/Internal/Arrays.lean) |
| `runtime-array-abi` | `ArrayAbi` | `array-abi-generate` | [`Internal/Arrays`](../../Solcore/Synthesis/Internal/Arrays.lean) |
| `runtime-closure-captures` | `ClosureCaptures` | `closure-captures-generate` | [`Internal/Captures`](../../Solcore/Synthesis/Internal/Captures.lean) |
| `runtime-closure-factories` | `ClosureFactories` | `closure-factories-generate` | [`Internal/Captures`](../../Solcore/Synthesis/Internal/Captures.lean) |

Each stateful profile has a case tool of its own. The five two-contract profiles (`stateful-calls`,
`stateful-forwarded-value`, `stateful-call-returns`, `stateful-call-sequences`,
`stateful-call-branches`) run through the call runner, the others through the storage runner.

| Profile | Namespace | Tool | File |
| --- | --- | --- | --- |
| `stateful-storage` | `Storage` | `semantic-storage-tool` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-storage-rollback` | `StorageRollback` | `semantic-storage-rollback-tool` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-keyed-storage` | `KeyedStorage` | `semantic-keyed-storage-tool` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-mapping` | `StorageMapping` | `semantic-mapping-tool` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-ledger` | `StorageLedger` | `semantic-ledger-tool` | [`Internal/Storage`](../../Solcore/Synthesis/Internal/Storage.lean) |
| `stateful-storage-loops` | `StorageLoop` | `semantic-storage-loop-tool` | [`Internal/StorageLoops`](../../Solcore/Synthesis/Internal/StorageLoops.lean) |
| `stateful-keccak-loops` | `KeccakLoop` | `semantic-keccak-loop-tool` | [`Internal/StorageLoops`](../../Solcore/Synthesis/Internal/StorageLoops.lean) |
| `stateful-assembly-storage-loops` | `AssemblyStorageLoop` | `semantic-assembly-storage-loop-tool` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `stateful-assembly-keccak-loops` | `AssemblyKeccakLoop` | `semantic-assembly-keccak-loop-tool` | [`Internal/Assembly`](../../Solcore/Synthesis/Internal/Assembly.lean) |
| `stateful-adt-storage` | `AdtStorage` | `semantic-adt-storage-tool` | [`Internal/AdtStorage`](../../Solcore/Synthesis/Internal/AdtStorage.lean) |
| `stateful-logs` | `EventLog` | `semantic-log-tool` | [`Internal/AdtStorage`](../../Solcore/Synthesis/Internal/AdtStorage.lean) |
| `stateful-calls` | `NestedCall` | `semantic-call-tool` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-call-value` | `CallValue` | `semantic-call-value-tool` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-forwarded-value` | `ForwardedCall` | `semantic-forward-tool` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-methods` | `Methods` | `semantic-methods-tool` | [`Internal/Calls`](../../Solcore/Synthesis/Internal/Calls.lean) |
| `stateful-call-returns` | `CallReturn` | `semantic-call-return-tool` | [`Internal/CallReturns`](../../Solcore/Synthesis/Internal/CallReturns.lean) |
| `stateful-call-sequences` | `CallSequence` | `semantic-call-sequence-tool` | [`Internal/CallReturns`](../../Solcore/Synthesis/Internal/CallReturns.lean) |
| `stateful-call-branches` | `CallBranch` | `semantic-call-branch-tool` | [`Internal/CallReturns`](../../Solcore/Synthesis/Internal/CallReturns.lean) |
| `stateful-constructor-arguments` | `ConstructorArguments` | `semantic-constructor-argument-tool` | [`Internal/ConstructorArguments`](../../Solcore/Synthesis/Internal/ConstructorArguments.lean) |
| `stateful-bytes-returns` | `BytesReturn` | `semantic-bytes-return-tool` | [`Internal/AbiReturns`](../../Solcore/Synthesis/Internal/AbiReturns.lean) |
| `stateful-tuple-returns` | `TupleReturn` | `semantic-tuple-return-tool` | [`Internal/AbiReturns`](../../Solcore/Synthesis/Internal/AbiReturns.lean) |
| `stateful-array-returns` | `ArrayReturn` | `semantic-array-return-tool` | [`Internal/AbiReturns`](../../Solcore/Synthesis/Internal/AbiReturns.lean) |
| `stateful-enum-returns` | `EnumReturn` | `semantic-enum-return-tool` | [`Internal/EnumAbi`](../../Solcore/Synthesis/Internal/EnumAbi.lean) |
| `stateful-enum-arguments` | `EnumArgument` | `semantic-enum-argument-tool` | [`Internal/EnumAbi`](../../Solcore/Synthesis/Internal/EnumAbi.lean) |
| `stateful-enum-array-arguments` | `EnumArray` | `semantic-enum-array-tool` | [`Internal/EnumAbi`](../../Solcore/Synthesis/Internal/EnumAbi.lean) |
| `stateful-dynamic-array` | `DynamicArray` | `semantic-dynamic-array-tool` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-bytes` | `DynamicBytes` | `semantic-bytes-tool` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-long-bytes` | `LongBytes` | `semantic-long-bytes-tool` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-nested-array` | `NestedArray` | `semantic-nested-array-tool` | [`Internal/AbiValues`](../../Solcore/Synthesis/Internal/AbiValues.lean) |
| `stateful-malformed-calldata` | `MalformedCalldata` | `semantic-malformed-calldata-tool` | [`Internal/Malformed`](../../Solcore/Synthesis/Internal/Malformed.lean) |
| `stateful-malformed-bytes` | `MalformedBytes` | `semantic-malformed-bytes-tool` | [`Internal/Malformed`](../../Solcore/Synthesis/Internal/Malformed.lean) |
| `stateful-malformed-nested-array` | `MalformedNestedArray` | `semantic-malformed-nested-array-tool` | [`Internal/Malformed`](../../Solcore/Synthesis/Internal/Malformed.lean) |

[`scripts/SEMANTIC_DIFFERENTIAL.md`](../../scripts/SEMANTIC_DIFFERENTIAL.md) says what each profile
generates and compares, and which backends it runs on.

## Definitions and theorems you build on

- **Sealed checked programs.** `CheckedWordProgram` and each family's `CheckedPlan`,
  `CheckedScenario` or `CheckedDAG` have a private constructor, so only the family's admission in
  the same file, which runs the full Core checker, builds one. `CheckedWordProgram.wellTyped` turns
  the check into Core typing through Core's `Wire.Program.check_full_sound`. Nothing else is proved
  about a profile without a theorem below.
- **The case format.** Each profile's `caseSchema`, plan schema and versions (`profileVersion`,
  `generatorVersion`, `emitterVersion`, `wrapperVersion`) are recorded in its cases and corpora.
  `replayCase` requires the versions to match, re-checks the plan, re-emits the source and
  compares it; it never trusts a saved result. The case tools print this JSON, the Python adapters
  validate its shape, and `scripts/semantic-*-corpus.json` stores it.
- **`Sequence.maxTransactions`** bounds a scenario, here and in `Tests/RustHull*ScenarioRun.lean`.
- **The emitter theorems.** Each says: if the emitter succeeds, calling `run` on the emitted text
  under the source semantics, which lexes and parses it, gives what the original Core computes.
  Pure ones conclude `CoreReturns` or `CoreReturnsWithStore`, over Core's `Program.runStateful`;
  stateful ones cover one top-level transaction of the installed contract and conclude
  `CoreCommits`, `CoreSettles` or `CoreLogs`, over ContractRuntime's `TopLevelExecution.run`. A
  change to either machine can break them. Each `emit_preserves_meaning` is the same result with
  the parsed file exposed. The [design note](../design/scalar-emitter-meaning.md) states each
  theorem, its assumptions and the emitters still open; README's Differential testing section cites
  them. `<Name>.emit_source_meaning`, in `Solcore.Synthesis.Source.ScalarMeaning`, is about
  `<Name>.emit` in the profile's file; `closed-g0`'s are `emit_source_meaning` and `emit`:
  - `PureTheorems`: `closed-g0`, `Input` (`runtime-word`), `Function`, `Primitive`, `Mutation`,
    `CallGraph`, `Aggregate`, `AggregateCallGraph`;
  - `LoopTheorems`: `Loop` (`runtime-loops`), `CallGraphLoop`, `Generic`;
  - `StatefulTheorems`: `Storage`, `StorageRollback`, `KeyedStorage`, `EventLog`
    (`stateful-logs`).

## Making changes

### Add a profile

`6b2f86b99` added two pure profiles (`runtime-checked-arithmetic`, `runtime-shifts`) and
`a07a8d021` a stateful one (`stateful-call-branches`). Their modules are now sections of
`Internal/Integers` and `Internal/CallReturns`, and their tests sections of
`Solcore/Test/Synthesis/Scalars.lean` and `Calls.lean`.

1. **Definitions first.** Record the probe and the profile's definitions in the
   [roadmap](../design/next-implementation-roadmap.md) before any profile code, as `acadc607a` did.
2. **Lean sections** in the family's `Internal/` file, or in a new file for a new family (import a
   new pure family from [`Solcore/Synthesis/Source.lean`](../../Solcore/Synthesis/Source.lean), as
   the others are):
   - `Core.<Name>`: the plan, its Core reference, generation from a `Seed`, reductions, and a
     sealed checked plan whose admission runs the Core checker;
   - `Source.<Name>`: the emitter, with its own `emitterVersion`, returning `EmittedProgram` (or a
     record of the family's own, such as `EmittedContracts` for two contracts);
   - for a stateful profile, `Stateful.<Name>Execution`: the transactions on ContractRuntime;
   - the cases in the profile's namespace: `caseSchema`, `generateCases`, `emitCase`,
     `replayCase`, `shrinkCases`, `observe` (`Source.CheckedArithmetic` is short).
3. **Case tool.**
   - Pure: in [`Tests/SemanticCaseTool.lean`](../../Tests/SemanticCaseTool.lean), import the file
     and add the `<name>-generate` entry of `generator`, a bound in `maximumNodes` if it is not 512,
     the `<name>-emit` command, the schema's branches in `observe`, `replay` and `shrink`, and the
     usage text.
   - Stateful: a new `Tests/Semantic<Name>Tool.lean`, its `lean_exe` in
     [`lakefile.lean`](../../lakefile.lean), and its entry in `TARGETS` of
     `scripts/prepare-semantic-tools.py`.
4. **Lean tests,** as sections of the family's file in `Solcore/Test/Synthesis/`, each registered
   in `Tests/Main.lean` (see [Tests](tests.md)):
   - pure: a cases test with golden sources and results from an independent model
     (`Tests.SourceIntegerCases`);
   - stateful: golden, cases and corpus tests (`Tests.SourceCallBranchGolden`, `…Cases`,
     `…Corpus`). The corpus test reads the fixed corpus.
5. **Runner registration.**
   - Pure: in `scripts/semantic-differential.py`, the schema in `CASE_PROFILES` and
     `CASE_CONTRACTS`, the plan's validation, the plan key in `validate_replayed_case`, and
     `REVERTING_SCHEMAS` if the reference can revert; in `scripts/semantic-campaign.py`,
     `PROFILE_COMMANDS`, the version fields and the coverage.
   - Stateful: an entry in `PROFILES` of `scripts/semantic-storage-differential.py` or
     `scripts/semantic-call-differential.py`, and its support in `semantic-storage-campaign.py` or
     `semantic-call-campaign.py`.
   - Both: `PROFILES` in `scripts/semantic-suite.py`: the manifest stem, the campaign family and the
     default random node budget.
6. **Corpus.** `scripts/<stem>-corpus.json`, and for a pure profile a validator
   `Tests/scripts/test-semantic-<name>-corpus.py`.
7. **Script tests.** Extend the adapter's and the campaign's tests. `scripts/test-semantic-suite.py`
   and `scripts/test-export-rust-yul.py` pin profile and case counts, and stateful profiles have
   also needed changes to `test-semantic-yul.py` and `test-semantic-fuzz.py`. Run every
   `scripts/test-semantic-*.py`.
8. **Docs.** With the results: the profile's section of `scripts/SEMANTIC_DIFFERENTIAL.md` and the
   roadmap's record (`eab3114ec`), then the shared counts in README's Differential testing,
   `scripts/SEMANTIC_CI.md` and the roadmap (`57b9c55c3`). Add the profile's row to this page.

### Change what an emitter prints

`acbbc4033` made the aggregate renderer print raw primitives, for eleven profiles.

1. Find every profile whose emitter uses what you change. `AggregateRenderer`
   (`Internal/Aggregates`) is used by most families; `git grep AggregateRenderer.` lists them.
2. Bump each affected profile's `emitterVersion` and `profileVersion`, so that older saved cases
   fail their version check instead of replaying under the new text.
3. Regenerate the fixed corpora of those profiles, and update the golden sources in their Lean
   tests and corpus validators.
4. If the emitter has a theorem, update its proof: the `*_render_spec` induction in
   `Source/ScalarMeaning/Internal/` and the profile's `emit_preserves_meaning`. A new printed form
   also needs the grammar, its round trip, and possibly the semantics.

### Prove an emitter's meaning

`143b0343b` and `cfa7783c1` did this for event logs, and `ce9d19a91` for keyed storage.

1. If the text uses forms outside the existing fragments, add a fragment: its statements and meaning
   in `FragmentSemantics` (or a file of its own, as `LogSemantics`), its text in the grammar file of
   its kind, and the `parse…Source_print` round trip.
2. Prove `<Name>.emit_preserves_meaning` and `<Name>.emit_source_meaning` in the theorem file of its
   kind, with lemmas in `Source/ScalarMeaning/Internal/`.
3. Add an executable check to `Solcore/Test/Synthesis/SourceMeaning.lean`: it runs actual emitter
   output through the source semantics and compares it with Core. Register it in `Tests/Main.lean`.
4. Update the design note's table, README's Differential testing paragraph and the list above.

## Pitfalls

- **Saved cases replay exactly.** The fixed corpora regenerate from their seeds, so G0 revision
  `v1` stays bit for bit; a different draw is a new `GeneratorRevision`. Replay regenerates a
  generated case from its seed and compares. Bump a profile's versions whenever its generation or
  its text changes.
- **The emitted text is the test input.** A renderer change changes the cases of every profile
  that uses it, and their corpora. Where no theorem covers an emitter, it is trusted: Core typing of
  a checked plan says nothing about what the emitter prints.
- **The kernel check visits only `Source/ScalarMeaning/`, and all of it.** Words such as
  `partial`, `axiom` or `sorry` fail there even in comments; see
  [Conventions](conventions.md#proof-rules).
- **Some files stay apart.** Each fragment's `*Semantics` derives `Repr`, whose matcher has the
  same shape as that of `tokens` in its grammar file; in one file Lean would reuse it, and the
  `tokens` equation lemmas would take their binder names from `Repr`. `LogSemantics` stays apart
  from `FragmentSemantics` because `loadMeaning` would lend its matcher to `memoryLoadMeaning`.
- **`lake build Solcore.Synthesis` does not build everything.** The umbrella reaches neither
  `Source/ScalarMeaning/` nor `Internal/AbiReturns`, `CallReturns`, `ConstructorArguments`,
  `EnumAbi` and `Malformed`. Build those by module name; `lake build` and `lake test` reach all.
- **Tools are separate targets.** `lake build` builds the library, not the case tools. The corpus
  validators run the tools in `.lake/build/bin/` by default, so rebuild a tool after a change.

## Testing

| Test file (in `Solcore/Test/Synthesis/` unless named) | Covers |
| --- | --- |
| [`Generators`](../../Solcore/Test/Synthesis/Generators.lean) | Seeds, the G0 fragment and its revisions, reductions, acceptance, seeded inputs, `closed-g0`, stateful sequences |
| [`Scalars`](../../Solcore/Test/Synthesis/Scalars.lean) | `runtime-word`, `-functions`, `-primitives`, `-mutation`, `-generics`, `-comptime`, `-modules`, `-checked-arithmetic`, `-shifts` |
| [`Aggregates`](../../Solcore/Test/Synthesis/Aggregates.lean) | `runtime-aggregates`, `-aggregate-call-graphs`, `-closures`, `-loop-closures` |
| [`CallGraphs`](../../Solcore/Test/Synthesis/CallGraphs.lean) | `runtime-call-graphs`, `-call-graph-loops`, `-recursion`, `-recursive-loops`, `stateful-calls` |
| [`Loops`](../../Solcore/Test/Synthesis/Loops.lean) | `runtime-loops`, `-nested-loops`, the three runtime assembly profiles, the storage and Keccak loops and their assembly forms |
| [`Enums`](../../Solcore/Test/Synthesis/Enums.lean) | `runtime-enums`, `stateful-enum-returns`, `-enum-arguments`, `-enum-array-arguments` |
| [`Traits`](../../Solcore/Test/Synthesis/Traits.lean) | `runtime-traits`, `-trait-hierarchies`, `stateful-methods` |
| [`Memory`](../../Solcore/Test/Synthesis/Memory.lean) | `runtime-memory-values`, `-memory-calls` |
| [`EventsAndReverts`](../../Solcore/Test/Synthesis/EventsAndReverts.lean) | `runtime-revert-data`, `-halts`, `stateful-logs` |
| [`Arrays`](../../Solcore/Test/Synthesis/Arrays.lean) | `runtime-memory-arrays`, `-array-abi`, `stateful-array-returns`, `-dynamic-array`, `-nested-array` |
| [`Captures`](../../Solcore/Test/Synthesis/Captures.lean) | `runtime-closure-captures`, `-closure-factories` |
| [`Bytes`](../../Solcore/Test/Synthesis/Bytes.lean) | `stateful-bytes-returns`, `-tuple-returns`, `-bytes`, `-long-bytes` |
| [`Storage`](../../Solcore/Test/Synthesis/Storage.lean) | `stateful-storage`, `-storage-rollback`, `-keyed-storage`, `-mapping`, `-ledger`, `-adt-storage` |
| [`Calls`](../../Solcore/Test/Synthesis/Calls.lean) | `stateful-call-value`, `-forwarded-value`, `-call-returns`, `-call-sequences`, `-call-branches`, `-constructor-arguments` |
| [`Malformed`](../../Solcore/Test/Synthesis/Malformed.lean) | The three malformed-calldata profiles |
| [`SourceMeaning`](../../Solcore/Test/Synthesis/SourceMeaning.lean) | The emitter theorems' definitions on actual emitter output |
| [`Solcore/Test/SourceCallReturnGolden`](../../Solcore/Test/SourceCallReturnGolden.lean) | The golden rows of `stateful-call-returns`, which `scripts/test-semantic-call-differential.py` also reads |

```sh
lake build Solcore.Synthesis                                          # front and most families
lake build Solcore.Synthesis.Internal.Integers                        # one family
lake build Solcore.Synthesis.Source.ScalarMeaning.StatefulTheorems    # every emitter proof
lake build Solcore.Test.Synthesis.Scalars                             # one test file's build checks
lake test                                                             # all IO tests
lake build semanticCaseTool && python3 Tests/scripts/test-semantic-shift-corpus.py
node scripts/check-kernel.mjs                                         # after touching ScalarMeaning
```

[Workflow](workflow.md#when-you-touch-the-differential-tests) covers the tool preparation, the
script tests and the suites, and `scripts/SEMANTIC_DIFFERENTIAL.md` each profile's suite commands.
