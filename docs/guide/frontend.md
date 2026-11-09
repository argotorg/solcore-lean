# Frontend

`Solcore/Frontend` compiles programs to Core. It holds two compilers and an older chain of
adapters:

- **The native pipeline** takes a `Workspace.RawWorkspace` of source files and produces checked
  programs, a closed specialization plan, Core code and sessions. Its public API is
  [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean).
- **Rust Hull** imports the typed Hull that the pinned solcore-rs exports, runs it on the Core
  machine, and proves its safety and, for part of it, its meaning. Its entry point is
  [`RustHull`](../../Solcore/Frontend/RustHull.lean).
- **Fragments** are the historical adapters. Nothing in the pipeline imports them, and they stay
  because tests use them.

The [umbrella](../../Solcore/Frontend.lean) imports the pipeline (through
[`Current`](../../Solcore/Frontend/Current.lean)) and the fragments, but not Rust Hull.

- **What it builds on.** [Syntax](syntax.md) for parsing; [Foundations](foundations.md) for the
  workspace, resolved names, source types and the ABI; [Core](core.md) as the target. The pipeline
  also imports two files of the source semantics: `SourceSemantics/CaptureBinders` and
  `SourceSemantics/Staging/Classification`.
- **What builds on it.** The [source semantics](source-semantics.md) is stated over the typed IR of
  `SourceInference/TypedIR`. [Core lowering](core-lowering.md) proves, for part of the language,
  that the native lowering preserves meaning, with theorems stated over the actual compiler
  functions. The generators of [Synthesis](synthesis.md) import `RustHull/Precompiles` for Keccak.
  The tests and README use the public APIs.

## Where things are

### Native pipeline

A program flows down this table. `checkProgram` loads it (validating the workspace, parsing each
file through `Syntax/Unchecked`, building the declaration environment), resolves imports, types and
signatures, and checks every function and method body. `SourceCoreCompiler.compileChecked` then
plans the specializations of the requested roots, validates the plan, and compiles one cached Core
artifact. `SourceCoreExecution.prepare` turns that artifact into the recipe that sessions run.

| File | Holds |
| --- | --- |
| **Public API** | |
| [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean) | Re-exports `SourceCoreExecution`; add a public name to its `export` lists |
| [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) | `compile`, `compileChecked`, `compileEntry`, `compileStaticWord`, `Compiled`, `Artifact`, `Session`, `Checkpoint`, `Outcome` |
| [`Current`](../../Solcore/Frontend/Current.lean) | Imports every stage of the pipeline; declares nothing |
| **Loading and checking** | |
| [`WordLiteral`](../../Solcore/Frontend/WordLiteral.lean) | `NumericLiteralDenotes`, `numericLiteralValue?`, `WordLiteralDenotes`, `interpretWordLiteral?` |
| [`ProgramInterfaces`](../../Solcore/Frontend/ProgramInterfaces.lean) | Identities, the declaration catalog `ProgramEnvironment`, interfaces, and loading: `loadProgram`, `ProgramLoadError` |
| [`ProgramImports`](../../Solcore/Frontend/ProgramImports.lean) | `ProgramImports`, `buildProgramImports`, `ProgramImportError` |
| [`ProgramTypeResolution`](../../Solcore/Frontend/ProgramTypeResolution.lean) | `ProgramTypeScope`, `validateProgramTypeScope`, `ProgramTypeResolutionError` |
| [`ProgramSignatures`](../../Solcore/Frontend/ProgramSignatures.lean) | `ProgramFunctionSignature`, `ProgramPredicate`, `ProgramSignatures` |
| [`ProgramSignatureFormation`](../../Solcore/Frontend/ProgramSignatureFormation.lean) | `ProgramSignatureFormationValidated`, `ProgramSignatureFormationError` |
| [`TraitResolution`](../../Solcore/Frontend/TraitResolution.lean) | The tabled trait search and its typed instance: `TraitResolution.Evidence`, `TypedTraitResolution.Evidence` |
| [`SourceInference/TypedIR`](../../Solcore/Frontend/SourceInference/TypedIR.lean) | The typed IR: `TypedSource`, `ExpressionNode`, `ExpressionForm`, `TypedBinder` |
| [`SourceInference/Types`](../../Solcore/Frontend/SourceInference/Types.lean) | `State`, `Context`, `CheckedFunction`, `SolvedRequirement`, `Error` |
| [`SourceInference/Resolution`](../../Solcore/Frontend/SourceInference/Resolution.lean) | Operator, overload and trait selection: `binaryOperatorDispatch`, `inferBinaryOperator`, `withExpected` |
| [`SourceInference/Expression`](../../Solcore/Frontend/SourceInference/Expression.lean) | The traversal `inferExprFuel`, `inferStatementFuel`, `inferStatementsFuel`, with the shift and unchecked branches |
| [`SourceInference/Program`](../../Solcore/Frontend/SourceInference/Program.lean) | `checkFunctionBody`, `finalize` |
| [`SourceInference`](../../Solcore/Frontend/SourceInference.lean) | The inference umbrella, which also imports five of its proof files |
| [`ProgramChecking`](../../Solcore/Frontend/ProgramChecking.lean) | `checkProgram`, `CheckedProgram`, `ProgramCheckError` |
| **Staging and specialization** | |
| [`SourceStageAnalysis`](../../Solcore/Frontend/SourceStageAnalysis.lean) | `SourceStageAnalysis.analyzeFunction`, `Stage`, and the staged values `SourceStagedValue.Value` |
| [`SourceSpecialization`](../../Solcore/Frontend/SourceSpecialization.lean) | `SpecializationKey`, `SpecializedFunction` |
| [`SourceSpecializationWorklist`](../../Solcore/Frontend/SourceSpecializationWorklist.lean) | `SourceSpecializationWorklist.run`, `Plan`, `Request` |
| [`ExecutableImplMethods`](../../Solcore/Frontend/ExecutableImplMethods.lean) | `ExecutableImplMethods.CheckedMethod` |
| [`SourceCompilationPlan`](../../Solcore/Frontend/SourceCompilationPlan.lean) | `exactSpecialization`, `exactInstantiationKey`, `validateExecutablePlanEvidence` |
| **Elaboration and lowering** | |
| [`SourceCoreElaboration`](../../Solcore/Frontend/SourceCoreElaboration.lean) | Literal evidence, closed types, elaboration errors; Core operators for source operators |
| [`SourceCore/Lowering`](../../Solcore/Frontend/SourceCore/Lowering.lean) | Scalars, locals, control, loops, assignments, calls and function values, by section: `SourceCorePrimitive`, `SourceCoreAssignments`, `SourceCoreSourceCells`, `SourceCoreFunctions` and others |
| [`SourceCore/Data`](../../Solcore/Frontend/SourceCore/Data.lean) | `SourceCoreDataCatalog.Catalog`: closed data, equality and defaults |
| [`SourceCore/DataExpressions`](../../Solcore/Frontend/SourceCore/DataExpressions.lean), [`DataPlaces`](../../Solcore/Frontend/SourceCore/DataPlaces.lean) | Data leaves, and places as Core getters and updaters (`SourceCoreDataPlaces.lower`) |
| [`SourceCore/GeneralFunctions`](../../Solcore/Frontend/SourceCore/GeneralFunctions.lean) | Matches, evidence, local polymorphism, staging contracts, general functions |
| [`SourceCore/RawMetadata`](../../Solcore/Frontend/SourceCore/RawMetadata.lean) | `SourceCoreRawMetadata.Registry` |
| [`SourceCore/CompatibleCatalog`](../../Solcore/Frontend/SourceCore/CompatibleCatalog.lean), [`Compatible`](../../Solcore/Frontend/SourceCore/Compatible.lean), [`CompatibleFunctions`](../../Solcore/Frontend/SourceCore/CompatibleFunctions.lean) | The source-compatible profile: catalog, values, data leaves and places, patterns, inputs, functions |
| [`SourceCoreUnified`](../../Solcore/Frontend/SourceCoreUnified.lean) | `SourceCoreUnifiedCompilation.Compiled`, the one cached artifact, and its runtime adapter |
| [`SourceCoreCompiler`](../../Solcore/Frontend/SourceCoreCompiler.lean) | `compileChecked`, `compile`, `Options`, `Error`, for an ordered root set |
| [`SourceCoreIndexedSession`](../../Solcore/Frontend/SourceCoreIndexedSession.lean) | `Recipe`, `Artifact`, `Session`, `Checkpoint`: persistent typed Core sessions |
| [`SourceCoreLegacyHeapImport`](../../Solcore/Frontend/SourceCoreLegacyHeapImport.lean) | A migration adapter, kept out of the public API |

The proofs are in three `Internal/` directories. A new lemma goes in the file of its topic.

| File | Topic |
| --- | --- |
| [`Internal/CheckingProperties`](../../Solcore/Frontend/Internal/CheckingProperties.lean) | What signature formation and trait resolution guarantee |
| [`Internal/RuntimeValues`](../../Solcore/Frontend/Internal/RuntimeValues.lean), [`RuntimeValidation`](../../Solcore/Frontend/Internal/RuntimeValidation.lean) | Source values, heap observations and bounded input validation; heap typing, deep validation and static lookup provenance |
| [`Internal/SignatureProperties`](../../Solcore/Frontend/Internal/SignatureProperties.lean) | What signature collection guarantees |
| [`Internal/SpecializationProperties`](../../Solcore/Frontend/Internal/SpecializationProperties.lean) | What specialization retains, for the source semantics |
| [`SourceInference/Internal/Continuations`](../../Solcore/Frontend/SourceInference/Internal/Continuations.lean) | Statement, `match` and `for` positions keep their inference calls |
| [`SourceInference/Internal/DirectCallInference`](../../Solcore/Frontend/SourceInference/Internal/DirectCallInference.lean), [`DirectCallOrigins`](../../Solcore/Frontend/SourceInference/Internal/DirectCallOrigins.lean), [`DirectCallPredicates`](../../Solcore/Frontend/SourceInference/Internal/DirectCallPredicates.lean) | Direct-call requirements: the traversals that establish their invariants; their declaration-call emitters; their ledger rows, declarations and predicates |
| [`SourceInference/Internal/ExpressionProperties`](../../Solcore/Frontend/SourceInference/Internal/ExpressionProperties.lean) | State preservation through the inference traversals |
| [`SourceInference/Internal/LocalGeneralization`](../../Solcore/Frontend/SourceInference/Internal/LocalGeneralization.lean), [`LocalGeneralizationBounds`](../../Solcore/Frontend/SourceInference/Internal/LocalGeneralizationBounds.lean) | Generalized bindings keep their inference action; the bounded event traversal |
| [`SourceInference/Internal/LocalReadOrigins`](../../Solcore/Frontend/SourceInference/Internal/LocalReadOrigins.lean), [`LocalReadScopes`](../../Solcore/Frontend/SourceInference/Internal/LocalReadScopes.lean) | Local references keep their lookup; no reference to a retired local |
| [`SourceInference/Internal/NodeGraph`](../../Solcore/Frontend/SourceInference/Internal/NodeGraph.lean) | The node table's graph, and agreement of results across fuel |
| [`SourceInference/Internal/OccurrenceProperties`](../../Solcore/Frontend/SourceInference/Internal/OccurrenceProperties.lean), [`RequirementProperties`](../../Solcore/Frontend/SourceInference/Internal/RequirementProperties.lean) | Occurrence allocation is monotone; obligation identities are preserved |
| [`SourceInference/Internal/ProgramProperties`](../../Solcore/Frontend/SourceInference/Internal/ProgramProperties.lean) | What finalization guarantees |
| [`SourceInference/Internal/SelectedCoercionPlanTrait`](../../Solcore/Frontend/SourceInference/Internal/SelectedCoercionPlanTrait.lean) | The trait of a selected coercion plan |
| [`SourceInference/Internal/StateProperties`](../../Solcore/Frontend/SourceInference/Internal/StateProperties.lean) | Allocation and lexical restoration of the typed state |
| [`SourceInference/Internal/TypedIRProperties`](../../Solcore/Frontend/SourceInference/Internal/TypedIRProperties.lean) | Final substitution preserves identities |
| [`SourceCore/Internal/Allocation`](../../Solcore/Frontend/SourceCore/Internal/Allocation.lean) | Allocation markers, fixed layouts, the source ledger, canonical contexts |
| [`SourceCore/Internal/Carriers`](../../Solcore/Frontend/SourceCore/Internal/Carriers.lean) | Heap markers and the Core frames of callable ancestry |
| [`SourceCore/Internal/CallableViews`](../../Solcore/Frontend/SourceCore/Internal/CallableViews.lean), [`CallablePrincipals`](../../Solcore/Frontend/SourceCore/Internal/CallablePrincipals.lean) | Source views of lambda reads and templates; cached principals of lambda declarations |
| [`SourceCore/Internal/CallableAncestry`](../../Solcore/Frontend/SourceCore/Internal/CallableAncestry.lean), [`CallablePaired`](../../Solcore/Frontend/SourceCore/Internal/CallablePaired.lean), [`CallableIndexed`](../../Solcore/Frontend/SourceCore/Internal/CallableIndexed.lean) | Callable ancestry in one cell, with paired callers, and over an indexed table |
| [`SourceCore/Internal/CallableOutputs`](../../Solcore/Frontend/SourceCore/Internal/CallableOutputs.lean) | Reverse values, heap exports and the public output codec |
| [`SourceCore/Internal/DirectLinking`](../../Solcore/Frontend/SourceCore/Internal/DirectLinking.lean) | Closed direct-call linking, and `SourceCoreDirectLinking.validatePlan` |
| [`SourceCore/Internal/Entries`](../../Solcore/Frontend/SourceCore/Internal/Entries.lean) | Prepared entries, public values, the assignment policy |
| [`SourceCore/Internal/FaultSites`](../../Solcore/Frontend/SourceCore/Internal/FaultSites.lean) | Source diagnostics for Core language failures |

### Rust Hull

The specification gives Hull a meaning without Core's evaluator, although the effect files in
`Semantics/` reuse a few compiler definitions (see Pitfalls). The theorems connect it to the
compiler.

| File | Holds |
| --- | --- |
| **Specification** | |
| [`RustHull/Syntax`](../../Solcore/Frontend/RustHull/Syntax.lean) | `Ty`, `Expr`, `Stmt`, `Function`, `YulStmt`; the pin `upstreamCommit` |
| [`RustHull/Decode`](../../Solcore/Frontend/RustHull/Decode.lean) | `decode`, `decodeText`, `DecodeLimits`, `DecodeError` |
| [`RustHull/Semantics`](../../Solcore/Frontend/RustHull/Semantics.lean) | The independent meaning, `Semantics.EvalFunction`, over abstract effects `Semantics.ExternalSemantics` |
| [`Semantics/Memory`](../../Solcore/Frontend/RustHull/Semantics/Memory.lean), [`Digests`](../../Solcore/Frontend/RustHull/Semantics/Digests.lean), [`World`](../../Solcore/Frontend/RustHull/Semantics/World.lean), [`Accounts`](../../Solcore/Frontend/RustHull/Semantics/Accounts.lean) | Memory, copies and snapshots; Keccak, SHA-256, RIPEMD-160; storage, environment, logs, code images, account observation and lifecycle; account calls and their transport |
| [`Semantics/Layers`](../../Solcore/Frontend/RustHull/Semantics/Layers.lean), [`Frames`](../../Solcore/Frontend/RustHull/Semantics/Frames.lean) | The stacked effect layers; child frames, call modes, creation, revert and `YulSemantics` |
| **Compiler** | |
| [`RustHull/Memory`](../../Solcore/Frontend/RustHull/Memory.lean), [`Precompiles`](../../Solcore/Frontend/RustHull/Precompiles.lean) | Byte memory and logs (`Memory`, `Logs`) and digests and precompiles (`Keccak.hash`, `Precompiles.staticCall`) as Core code, with no Hull syntax |
| [`RustHull/LoweringSupport`](../../Solcore/Frontend/RustHull/LoweringSupport.lean) | `LowerM`, `LoweringError`, `Scope`, `Signature`, `CodeBuilder` |
| [`RustHull/Effects`](../../Solcore/Frontend/RustHull/Effects.lean) | Accounts, ambient observations, calls, creation (`CreationRuntime`), and the effect builtins |
| [`RustHull/Lowering`](../../Solcore/Frontend/RustHull/Lowering.lean) | `lowerExpression`, `lowerStatement`, `lowerBuiltin`, `lowerFunction`, `assemble`, and inline Yul (`YulLowering.lowerExpr`) |
| [`RustHull/CodeImage`](../../Solcore/Frontend/RustHull/CodeImage.lean) | Linked code images: `CodeImage.resolve`, `ObjectLinking.link`; the pin `backendRevision` |
| [`RustHull/AccountRuntime`](../../Solcore/Frontend/RustHull/AccountRuntime.lean) | Message frames: `AccountRuntime.compileFrame`, `MemorySnapshot` |
| [`RustHull/Contract`](../../Solcore/Frontend/RustHull/Contract.lean), [`LinkedContract`](../../Solcore/Frontend/RustHull/LinkedContract.lean), [`ScalarExecution`](../../Solcore/Frontend/RustHull/ScalarExecution.lean) | The entry points: `Contract.prepare`, `Contract.runWithReceipt`, `LinkedContract.prepareDeployment`, `ScalarExecution.prepare` |
| **Theorems** | |
| [`RustHull/Safety`](../../Solcore/Frontend/RustHull/Safety.lean) | Successful preparation excludes Core machine faults |
| [`RustHull/Correspondence`](../../Solcore/Frontend/RustHull/Correspondence.lean) | Meaning of functions and programs without external effects |
| [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean), [`ContractCodeTheorems`](../../Solcore/Frontend/RustHull/ContractCodeTheorems.lean), [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) | Meaning of contracts, one theorem per effect layer |

| `RustHull/Internal/` file | Topic |
| --- | --- |
| [`Derivations`](../../Solcore/Frontend/RustHull/Internal/Derivations.lean) | Simulation by induction on a finite Hull derivation, inline Yul included |
| [`Statements`](../../Solcore/Frontend/RustHull/Internal/Statements.lean) | Expressions, patterns, assignments and straight-line statements in the lowering output |
| [`NamedFunctions`](../../Solcore/Frontend/RustHull/Internal/NamedFunctions.lean), [`PublicFunctions`](../../Solcore/Frontend/RustHull/Internal/PublicFunctions.lean) | Function installation and calls; the public theorems for call-free functions |
| [`LoweringFacts`](../../Solcore/Frontend/RustHull/Internal/LoweringFacts.lean) | Shapes of the lowering output, literals, scope coverage, receipts |
| [`MemoryState`](../../Solcore/Frontend/RustHull/Internal/MemoryState.lean), [`StorageState`](../../Solcore/Frontend/RustHull/Internal/StorageState.lean) | Core memory, copies and logs, and Core storage, against the independent state |
| [`Digests`](../../Solcore/Frontend/RustHull/Internal/Digests.lean) | Core Keccak, SHA-256 and RIPEMD-160 against their independent definitions |
| [`EffectBuiltins`](../../Solcore/Frontend/RustHull/Internal/EffectBuiltins.lean), [`CallBuiltins`](../../Solcore/Frontend/RustHull/Internal/CallBuiltins.lean), [`CreationBuiltin`](../../Solcore/Frontend/RustHull/Internal/CreationBuiltin.lean) | The builtin compiler: state builtins; calls, revert and inline Yul; CREATE and CREATE2 |
| [`EffectLayers`](../../Solcore/Frontend/RustHull/Internal/EffectLayers.lean), [`TerminationLayers`](../../Solcore/Frontend/RustHull/Internal/TerminationLayers.lean), [`AccountLayers`](../../Solcore/Frontend/RustHull/Internal/AccountLayers.lean), [`CallEffects`](../../Solcore/Frontend/RustHull/Internal/CallEffects.lean) | Frame and message proofs, layer by layer (`compileFrame_preserves`) |
| [`RuntimeFrames`](../../Solcore/Frontend/RustHull/Internal/RuntimeFrames.lean), [`RuntimeObjects`](../../Solcore/Frontend/RustHull/Internal/RuntimeObjects.lean) | One compiled frame; object initialization and the code catalog |
| [`LinkedWorld`](../../Solcore/Frontend/RustHull/Internal/LinkedWorld.lean) | Catalog links and executable identities survive call-free operations |
| [`CallLayout`](../../Solcore/Frontend/RustHull/Internal/CallLayout.lean), [`CallStates`](../../Solcore/Frontend/RustHull/Internal/CallStates.lean), [`CallTransport`](../../Solcore/Frontend/RustHull/Internal/CallTransport.lean) | The call layer's layout and state relation; its resources and callbacks; caller-frame transport and the identity precompile |
| [`AccountCalls`](../../Solcore/Frontend/RustHull/Internal/AccountCalls.lean), [`ChildFrames`](../../Solcore/Frontend/RustHull/Internal/ChildFrames.lean), [`ChildFrameCalls`](../../Solcore/Frontend/RustHull/Internal/ChildFrameCalls.lean) | Account dispatch and call modes; fresh child frames; finite call trees and root reentry |
| [`Creation`](../../Solcore/Frontend/RustHull/Internal/Creation.lean) | Addresses, handlers and transport of CREATE and CREATE2 |

### Fragments

[`Fragments`](../../Solcore/Frontend/Fragments.lean) imports these. They share only `WordLiteral`
with the pipeline, but their matches on the syntax operators need a case for each new operator.

| Topic | Files in `Fragments/Internal/` |
| --- | --- |
| Closed source, bodies and computations | [`ClosedSource`](../../Solcore/Frontend/Fragments/Internal/ClosedSource.lean), [`Computation`](../../Solcore/Frontend/Fragments/Internal/Computation.lean), [`ReturnBodies`](../../Solcore/Frontend/Fragments/Internal/ReturnBodies.lean), [`TypedLet`](../../Solcore/Frontend/Fragments/Internal/TypedLet.lean), [`RecursiveComputation`](../../Solcore/Frontend/Fragments/Internal/RecursiveComputation.lean) |
| Local expressions, applications and lambdas | [`LocalExpressions`](../../Solcore/Frontend/Fragments/Internal/LocalExpressions.lean), [`LocalApplication`](../../Solcore/Frontend/Fragments/Internal/LocalApplication.lean), [`LocalComputations`](../../Solcore/Frontend/Fragments/Internal/LocalComputations.lean), [`LocalFunctionApplication`](../../Solcore/Frontend/Fragments/Internal/LocalFunctionApplication.lean), [`Expected`](../../Solcore/Frontend/Fragments/Internal/Expected.lean), [`ExpectedLambdas`](../../Solcore/Frontend/Fragments/Internal/ExpectedLambdas.lean), [`LambdaDepth`](../../Solcore/Frontend/Fragments/Internal/LambdaDepth.lean) |
| Word operators, values and runtime functions | [`Foundations`](../../Solcore/Frontend/Fragments/Internal/Foundations.lean), [`SourceValues`](../../Solcore/Frontend/Fragments/Internal/SourceValues.lean), [`RuntimeFunctions`](../../Solcore/Frontend/Fragments/Internal/RuntimeFunctions.lean), [`RuntimeParameters`](../../Solcore/Frontend/Fragments/Internal/RuntimeParameters.lean) |

## Definitions and theorems you build on

| Item | Reading | Used by |
| --- | --- | --- |
| `SourceCompiler.compile`, `compileChecked`, `compileEntry`, `compileStaticWord`, `Compiled.open`, `Session.run`, `Checkpoint.resume` | The public API of the native compiler | README, the execution tests; core lowering's public theorems, such as `SelectedCompilationRawPublicReceipt.of_compile`, unfold `compile` |
| `checkProgram`, `CheckedProgram`, `SourceInference.TypedSource` | The checker and the typed IR it produces | The source semantics and core lowering |
| `SourceCoreCompiler.compile_checked_source`, `SourceCoreExecution.compile_checked_source`, `Compiled.plan_validated` | A compiled program is exactly the checker's output for its workspace, and its plan passed `validateExecutablePlanEvidence` | The source semantics, core lowering, tests |
| `checkProgram_success_signature_formation`, `checkProgram_success_method_body`, `SourceInference.checkFunctionBody_success_declaration` | What checking guarantees for signatures, methods and bodies | The source semantics, core lowering, tests |
| `SourceCoreIndexedSession.Recipe.prepare_compiled`, `SourceCoreCompiler.Compiled.artifact_fields`, `Session.start_indexed` | Recipes, artifacts and sessions come from the actual compilation | Core lowering, tests; the source semantics uses `artifact_fields` |
| `SourceSemantics.CaptureBinders.copiedBinder?` | Which binders a closure copies | One decision for the source semantics and `SourceCore/Lowering` |
| `Contract.prepare_resumes_safe`, `LinkedContract.prepare_resumes_safe`, `ScalarExecution.prepare_resumes_never_faults` | After successful preparation, no chain of resumptions hits a Core machine fault; language failures, reverts and exhausted fuel remain | README's Proof status |
| `Correspondence.prepare_recursive_program_resumes`, with `prepare_ranked_program_resumes` and `prepare_pure_program_resumes` | A finite independent evaluation of an eligible program relates its result and heap to every chain of public resumptions, which completes exactly when the fuel reaches the transition count | [Hull meaning preservation](../design/hull-meaning-preservation.md), tests |
| The `prepare_resumes_exact` and `compileObject_resumes_exact` theorems of `ContractMemoryCorrespondence`, `ContractCallModeCorrespondence` and the other layers | The same for contracts, one effect layer at a time, from actual compilation to public receipts | The Hull note, tests |

The source semantics and core lowering use none of the other results, such as
`checkProgram_success_unique_fuel`, `checkProgram_success_declarations_nodup`,
`Bootstrap.ready_indexed` and `SourceCoreUnifiedPreparationCertificates.run_done_specialization`.
The Hull note says what each meaning theorem assumes and what remains: the elliptic-curve
precompiles, creation with init frames, more of inline Yul, and object linking.

## Making changes

### A new construct in the native compiler

Worked examples: 5b8c6e96d (shifts) and e8d28e957 (`unchecked` blocks). Their paths are from before
the layout refactor; [Conventions](conventions.md#following-older-notes) says how to map them.
[Adding a language feature](adding-a-feature.md) covers the other layers.

1. **Syntax**, as [Syntax](syntax.md#making-changes) describes. A pass around the parser also
   needs `parseWorkspaceFile` in `ProgramInterfaces`, and a `ProgramLoadError` for its failures.
2. **Typed IR.** A new operator needs none: `ExpressionForm` carries `Syntax.BinaryOp` and
   `Syntax.ValueAssignOp`. A new form needs a constructor in `SourceInference/TypedIR`.
3. **Inference**, in `SourceInference/Resolution`: the dispatch (`binaryOperatorDispatch`) and the
   typing rule (`inferBinaryOperator`, whose shift branch runs before any dispatch). A new form also
   needs its arm in `inferExprFuel` (`SourceInference/Expression`).
4. **Inference proofs**: the new branch's lemmas next to it (`inferBinaryOperator_shift_result` in
   `SourceInference/Expression`), then every case analysis in
   `SourceInference/Internal/ExpressionProperties`. `unchecked` also touched `RequirementProperties`,
   `OccurrenceProperties`, `DirectCallOrigins` and `LocalReadOrigins`.
5. **Elaboration and lowering**: the Core operator in `SourceCoreElaboration` (`directBinary`,
   `stagedCoreBinary?`); in `SourceCore/Lowering`, `SourceCorePrimitive.strictBinaryBody` and
   `binaryOperandType`, `SourceCoreAssignments.operator?` and `wordOnly?`, and
   `SourceCoreInteger.strictBinaryBody`; the operator table and guard of
   `SourceCoreDataPlaces.lower` and of `SourceCore/Compatible`.
6. **Fragments and frontend tests**: their exhaustive matches, in `Fragments/Internal/Foundations`,
   `LocalExpressions`, `LocalFunctionApplication` and `RecursiveComputation`, and in the tests
   `ClosedStrictWords` and `ExpectedDataImages`.
7. **Semantics and proofs**: the [source semantics](source-semantics.md) and
   [core lowering](core-lowering.md). A new guard in the lowering becomes a premise there: since the
   data-place lowering refuses Word-only operators at `integer` leaves, the shared assignment
   premise reads `operator.wordOnly = false`.
8. **Tests**: a public-API test with a `run`, called from `Tests/Main.lean`, such as
   `Tests.SourceCoreShiftExecution` and `Tests.SourceCoreUncheckedExecution` in
   [`Foundations/Execution`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean).
   Give the expected values of the pinned Rust paths, and the programs that must be rejected.

### A change to what an existing construct compiles to

Worked example: 7ac75aea3, closures that capture by value.
- Put a decision that the semantics and the lowering both make in one function, low in the imports:
  `CaptureBinders.copiedBinder?` in `SourceSemantics/CaptureBinders`, which imports only
  `SourceInference/TypedIR`.
- Change the lowering (here the sections `SourceCoreSourceCells`, `SourceCoreFunctions` and
  `SourceCoreLoops` of `SourceCore/Lowering`) and the semantics together.
- Expect to restate the core lowering theorems that describe the old code; that commit restated
  every theorem about closure formation and calls, and updated the tests' expected results.

### A new public entry point

Define it in `SourceCoreExecution` and add it to the `export` lists of `SourceCompiler`.
`UnifiedCorpus` in `Solcore/Test/SourceSemantics/CoreLowering` checks the exports with `rfl`, and
`#check_failure` probes there and in `Source/Compiler` assert names that must stay absent.

### Rust Hull: executable support for a builtin or construct

Worked examples: 1ad29dadc (all opcode wrappers) and baacd0fb9 (account state operations).
1. A new node in the export: `RustHull/Syntax` and `RustHull/Decode`. The decoder rejects unknown
   fields, another schema and another upstream revision.
2. The compiler: `RustHull/Lowering` and `LoweringSupport`, the effect builtins in
   `RustHull/Effects`, frames in `AccountRuntime`, code images in `CodeImage`, and the boundaries in
   `Contract` and `LinkedContract`.
3. `RustHull/Safety` must still prove the safety theorems for the new code.
4. Tests in `Solcore/Test/Frontend/RustHull/`, with fixtures under `Tests/Fixtures/` and a runner
   or script when Rust output is compared, as `Tests/RustHullOpcodeWrappersRun.lean` and
   `scripts/test-rust-opcode-wrappers.py` are.

### Rust Hull: connecting a feature to the meaning theorems

Worked examples: c60b25309 (Yul word operations) and 0b178e54c (RIPEMD-160).
1. The independent rule: for Yul, `YulSemantics` in `Semantics/Frames`; for the precompile, its
   digest in `Semantics/Digests` and its dispatch in `Semantics/Accounts`.
2. The simulation in `RustHull/Internal/`: `Derivations` and `CallBuiltins` for Yul; `Digests` and
   `CallTransport` for the precompile.
3. The public theorem of the layer, and a consumer of it in the tests, such as those in
   `Solcore/Test/Frontend/RustHull/Effects`.
4. The status tables of the Hull note. Its completion rule: a feature is connected only when its
   independent derivation reaches the actual compiler and the public run and resume API.

### Rust Hull: an exporter change or a new pin

Worked examples: 7aa1d539d (the re-pin to `e2eef194`) and 32b38d908 (larger nested artifacts).
- In Lean: `RustHull.upstreamCommit`, `CodeImage.backendRevision` when the backend moves, the
  revision named in `RustHull/Lowering`'s inline-Yul section, and the sample export in
  `Solcore/Test/Frontend/RustHull/Effects`. Grep for the old revision. Raise `DecodeLimits` if
  exports grow.
- Outside Lean: the exporters and manifests; see [Differential testing](differential-testing.md)
  and [`scripts/RUST_PARITY.md`](../../scripts/RUST_PARITY.md). Moving the pin is a change of its
  own.

## Pitfalls

- **Core lowering reads the compiler's code.** Its proofs unfold compiler definitions and state
  premises in their terms. A change to a compiler function is a change to those proofs; plan it with
  the [core lowering](core-lowering.md) work.
- **Inference proofs number their cases.** They do functional induction on `inferExprFuel` and name
  its cases by number, in `SourceInference/Internal` and `SourceSemantics/Internal`. A new arm in
  `inferExprFuel`, or a new syntax constructor it matches on, shifts them. This is why `unchecked`
  is a pass around the parser.
- **The compiler imports the inference proofs.** `ProgramChecking` imports the `SourceInference`
  umbrella, which imports five proof files, so a broken inference proof stops the compiler build.
- **Files kept apart on purpose.** The layout refactor kept these apart, for these reasons:
  - `SourceCore/Internal/CallablePrincipals` stands alone: its private instances, which
    `CallableViews` also declares, must stay outside the closure of `Callable/CoercionSpine` in core
    lowering.
  - `SourceCore/Internal/Carriers` imports no source semantics, so that `CallableViewWrappers` in
    core lowering stays outside `Solcore.SourceSemantics.Context`.
  - `SourceCore/Data` stays below the lowering: core lowering imports it, and a wider closure changes
    its `simp` calls.
  - `Internal/SignatureProperties` stays out of reach of `SourceInference/Internal/ExpressionProperties`,
    whose proofs break once `ProgramFunctionSignature.parameterTypes_length` is a `simp` lemma there.
  - `DirectCallInference` and `DirectCallOrigins` each have a private `exceptPure_eq_ok` with its own
    proof.
  - `ProgramSignatures` and `ProgramSignatureFormation`, `Internal/RuntimeValues` and
    `RuntimeValidation`, `DataExpressions` and `DataPlaces`, and `Compatible` and
    `CompatibleFunctions` would share matchers in one file, which renames the variables of their
    equation lemmas.
- **Tests assert imports.** `#check_failure` probes keep `SourceCore/CompatibleCatalog` below the
  value encoder of `SourceCore/Compatible` (`Compatible/Payloads`) and `SourceCoreLegacyHeapImport`
  out of the public API (`UnifiedCorpus`). A new import can break them.
- **Hull files kept apart on purpose.**
  - `RustHull/Memory`, which holds `Logs`, and `RustHull/Precompiles` import no Hull syntax. The
    generators import `Precompiles`, and under `open Core` their `Expr` means `Core.Expr`, which
    `RustHull.Expr` would make ambiguous. The test file `RustHull/YulPrimitives` stays apart from
    `RustHull/Runtime` for the same reason.
  - `CreationRuntime` stays in `RustHull/Effects`, below `Lowering`: it uses `CodeBuilder.boolean`,
    and `Lowering` declares a `boolean` of its own.
  - `Internal/CallLayout` stays apart from `Internal/CallStates`: `call_fixed_separation` unfolds
    `Layout` millions of times, which costs a quarter more heartbeats, past the limit, when `Layout`
    is in the same file.
- **The Hull specification shares some compiler definitions.** `Semantics/World` uses
  `AccountState.Account` from `RustHull/Effects` and `Memory.packBytes` from `RustHull/Memory`, and
  `YulSemantics` uses `YulFragment.primitives` from `RustHull/Lowering`. Changing one of these
  changes the specification as well.
- **A frame result is not a public theorem.** `compileFrame_preserves` is a step towards a contract
  theorem, which starts at actual compilation and ends at public receipts.

## Testing

```sh
lake build Solcore.Frontend                          # the native pipeline and the fragments
lake build Solcore.Frontend.RustHull                 # the Hull importer, without its theorems
lake build Solcore.Frontend.RustHull.Safety          # the Hull safety theorems
lake build Solcore.Frontend.RustHull.Correspondence  # the function meaning theorems
lake build Solcore.Frontend.RustHull.ContractCallTheorems  # with the state and code theorems
lake test                                            # every test, through Tests/Main.lean
```

| Subject | Tests |
| --- | --- |
| Loading and checking | [`Programs`](../../Solcore/Test/Frontend/Programs.lean), [`PublicBoundary`](../../Solcore/Test/Frontend/PublicBoundary.lean), [`Source/Inference`](../../Solcore/Test/Frontend/Source/Inference.lean) |
| Staging, specialization, plans | [`Source/Specialization`](../../Solcore/Test/Frontend/Source/Specialization.lean), [`Source/Staged`](../../Solcore/Test/Frontend/Source/Staged.lean), [`Source/StagedIntegers`](../../Solcore/Test/Frontend/Source/StagedIntegers.lean), [`Source/CompilationPlan`](../../Solcore/Test/Frontend/Source/CompilationPlan.lean) |
| The public compiler and sessions | [`Source/Compiler`](../../Solcore/Test/Frontend/Source/Compiler.lean), [`Source/TypedRuntime`](../../Solcore/Test/Frontend/Source/TypedRuntime.lean), and the execution tests in [`Foundations/Execution`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean) |
| Rust Hull | [`Solcore/Test/Frontend/RustHull/`](../../Solcore/Test/Frontend/RustHull), the runners `Tests/RustHull*Run.lean`, the fixtures in `Tests/Fixtures/` |
| Fragments | The other files in [`Solcore/Test/Frontend/`](../../Solcore/Test/Frontend) |

`Tests/Main.lean` imports the test files and calls their `run` entry points. Some Hull runners are
executables of their own, such as
`rustHullScenario` (`lake build rustHullScenario`), and others run as scripts, such as
`lake env lean --run Tests/RustHullWorldRun.lean`. [Tests](tests.md) says how the tests are
organized.
