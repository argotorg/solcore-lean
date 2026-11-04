# Reviewer's guide: Frontend

`Solcore/Frontend` holds two compilers to Core, and an older chain that neither of them uses:

- **The native pipeline.** From a raw workspace to a checked program, a specialization plan, Core
  code and a session. Its entry point is [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean).
- **Rust Hull.** A separate import path for the typed Hull that the pinned Rust compiler exports.
  Its entry point is [`RustHull`](../../Solcore/Frontend/RustHull.lean), and it carries the area's
  main theorems.
- **Fragments.** The historical adapters. The pipeline reaches one module of this chain, the
  numeric literals, and Hull reaches none. Tests still use it, so it stays, and a reviewer can
  skip it.

The [umbrella](../../Solcore/Frontend.lean) gives this reading order in brief.

## Main definitions and theorems

Each entry has its evidence. **README** is "Proof status". **Hull note** is
[Hull meaning preservation](../design/hull-meaning-preservation.md), and **runtime note** is
[Core runtime unification](../design/core-runtime-unification.md). **Root** means that no other
declaration uses it and that it has one of the largest dependency closures of the area. **Path**
means that `SourceCoreExecution.compile` or `Session.run` reaches it.

| Item | Where | Evidence |
| --- | --- | --- |
| The public source API: `SourceCoreExecution.compile`, `Session.run`, `Checkpoint.resume` | [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean), [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) | README, runtime note |
| `SourceCoreExecution.compile_checked_source` and its entry and static Word variants | [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) | Root |
| `checkProgram` and `checkProgram_success_method_body` | [`ProgramChecking`](../../Solcore/Frontend/ProgramChecking.lean) | Root, Path |
| `SourceSpecializationWorklist.run`, `SourceCompilationPlan` | [`SourceSpecializationWorklist`](../../Solcore/Frontend/SourceSpecializationWorklist.lean), [`SourceCompilationPlan`](../../Solcore/Frontend/SourceCompilationPlan.lean) | Path |
| Hull syntax and decoding: `RustHull.Expr`, `RustHull.decodeText` | [`Syntax`](../../Solcore/Frontend/RustHull/Syntax.lean), [`Decode`](../../Solcore/Frontend/RustHull/Decode.lean) | README |
| The independent Hull meaning: `Semantics.EvalFunction` and the effect semantics | [`Semantics`](../../Solcore/Frontend/RustHull/Semantics.lean) and `RustHull/Semantics/` | Hull note |
| The Hull compiler: `lowerExpression`, `assemble`, `Contract.compileObject` | [`Lowering`](../../Solcore/Frontend/RustHull/Lowering.lean), [`Contract`](../../Solcore/Frontend/RustHull/Contract.lean) | Hull note, README |
| Public Hull entry points: `ScalarExecution.prepare`, `LinkedContract.prepareDeployment`, `Contract.runWithReceipt` | [`ScalarExecution`](../../Solcore/Frontend/RustHull/ScalarExecution.lean), [`LinkedContract`](../../Solcore/Frontend/RustHull/LinkedContract.lean), [`Contract`](../../Solcore/Frontend/RustHull/Contract.lean) | README |
| Hull execution safety: `Contract.prepare_resumes_safe`, `ScalarExecution.prepare_resumes_never_faults` | [`Safety`](../../Solcore/Frontend/RustHull/Safety.lean) | README, Hull note |
| Hull function meaning: `Correspondence.prepare_recursive_program_resumes` | [`Correspondence`](../../Solcore/Frontend/RustHull/Correspondence.lean) | Hull note, Root |
| Hull contract meaning: the `prepare_resumes_exact` and `compileObject_resumes_exact` theorems of each effect layer | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean), [`ContractCodeTheorems`](../../Solcore/Frontend/RustHull/ContractCodeTheorems.lean), [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) | Hull note, Root |

## Reading order

1. **Public API.** `SourceCompiler`, then `SourceCoreExecution`.
2. **Checking.** `ProgramInterfaces`, `ProgramImports`, `ProgramTypeResolution`, `ProgramSignatures`,
   `ProgramSignatureFormation`, `TraitResolution`, `SourceInference`, and `ProgramChecking` on top.
3. **Staging and specialization.** `SourceStageAnalysis`, `SourceSpecialization`,
   `SourceSpecializationWorklist` and `SourceCompilationPlan`.
4. **Lowering.** `SourceCoreElaboration`, then `SourceCore/`, then `SourceCoreUnified`,
   `SourceCoreCompiler` and `SourceCoreIndexedSession`.
5. **Rust Hull.** The syntax, the independent meaning, the compiler, and the main theorems.

Everything else is proof machinery in the `Internal/` directories.

## Native pipeline

### Public API

| File | Main declarations |
| --- | --- |
| [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean) | The public API of the native compiler, exported from `SourceCoreExecution` |
| [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) | `SourceCoreExecution.compile`, `SourceCoreExecution.compileChecked`, `SourceCoreExecution.compileEntry`, `SourceCoreExecution.compileStaticWord`, `SourceCoreExecution.Compiled`, `SourceCoreExecution.Artifact`, `SourceCoreExecution.Session`, `SourceCoreExecution.Checkpoint`, `SourceCoreExecution.Outcome` |
| [`Current`](../../Solcore/Frontend/Current.lean) | Imports every stage of the current whole-program pipeline |

### Checking

| File | Main declarations |
| --- | --- |
| [`WordLiteral`](../../Solcore/Frontend/WordLiteral.lean) | `NumericLiteralDenotes`, `numericLiteralValue?`, `WordLiteralDenotes`, `interpretWordLiteral?` |
| [`ProgramInterfaces`](../../Solcore/Frontend/ProgramInterfaces.lean) | `ProgramTraitId`, `ProgramImplId`, `BuiltinFunctionId`, `ProgramEnvironment`, `ProgramDeclaration` |
| [`ProgramImports`](../../Solcore/Frontend/ProgramImports.lean) | `ProgramImports`, `buildProgramImports`, `ProgramImportError` |
| [`ProgramTypeResolution`](../../Solcore/Frontend/ProgramTypeResolution.lean) | `ProgramTypeScope`, `validateProgramTypeScope`, `ProgramTypeResolutionError` |
| [`ProgramSignatures`](../../Solcore/Frontend/ProgramSignatures.lean) | `ProgramFunctionSignature`, `ProgramPredicate`, `ProgramSignatures` |
| [`ProgramSignatureFormation`](../../Solcore/Frontend/ProgramSignatureFormation.lean) | `ProgramSignatureFormationValidated`, `ProgramSignatureFormationError` |
| [`TraitResolution`](../../Solcore/Frontend/TraitResolution.lean) | `TraitResolution.Predicate`, `TraitResolution.Evidence`, `TypedTraitResolution.Evidence`, `TypedTraitResolution.TraitId`, `TypedTraitResolution.ImplId` |
| [`SourceInference/TypedIR`](../../Solcore/Frontend/SourceInference/TypedIR.lean) | `SourceInference.ExpressionId`, `SourceInference.TypedBinder`, `SourceInference.ExpressionNode`, `SourceInference.ExpressionForm`, `SourceInference.TypedSource` |
| [`SourceInference/Types`](../../Solcore/Frontend/SourceInference/Types.lean) | `SourceInference.State`, `SourceInference.Context`, `SourceInference.CheckedFunction`, `SourceInference.SolvedRequirement`, `SourceInference.Error` |
| [`SourceInference/Resolution`](../../Solcore/Frontend/SourceInference/Resolution.lean) | `SourceInference.Detail.withExpected`, `SourceInference.Detail.OperatorDispatch` |
| [`SourceInference/Expression`](../../Solcore/Frontend/SourceInference/Expression.lean) | `SourceInference.Detail.inferExprFuel`, `SourceInference.Detail.inferStatementFuel`, `SourceInference.Detail.inferStatementsFuel` |
| [`SourceInference/Program`](../../Solcore/Frontend/SourceInference/Program.lean) | `SourceInference.checkFunctionBody`, `SourceInference.Detail.finalize` |
| [`ProgramChecking`](../../Solcore/Frontend/ProgramChecking.lean) | `checkProgram`, `CheckedProgram`, `ProgramCheckError` |

### Staging and specialization

| File | Main declarations |
| --- | --- |
| [`SourceStageAnalysis`](../../Solcore/Frontend/SourceStageAnalysis.lean) | `SourceStageAnalysis.Analysis`, `SourceStageAnalysis.Stage`, `SourceStageAnalysis.analyzeFunction`, `SourceStagedValue.Value` |
| [`SourceSpecialization`](../../Solcore/Frontend/SourceSpecialization.lean) | `SourceSpecialization.SpecializationKey`, `SourceSpecialization.SpecializedFunction` |
| [`SourceSpecializationWorklist`](../../Solcore/Frontend/SourceSpecializationWorklist.lean) | `SourceSpecializationWorklist.run`, `SourceSpecializationWorklist.Plan`, `SourceSpecializationWorklist.Request` |
| [`ExecutableImplMethods`](../../Solcore/Frontend/ExecutableImplMethods.lean) | `ExecutableImplMethods.CheckedMethod` |
| [`SourceCompilationPlan`](../../Solcore/Frontend/SourceCompilationPlan.lean) | `SourceCompilationPlan.Key`, `SourceCompilationPlan.Error`, `SourceCompilationPlan.exactSpecialization`, `SourceCompilationPlan.exactInstantiationKey` |

### Lowering

These are the compiler functions that the theorems in `SourceSemantics/CoreLowering` describe. The
files read in dependency order.

| File | Main declarations |
| --- | --- |
| [`SourceCoreElaboration`](../../Solcore/Frontend/SourceCoreElaboration.lean) | `SourceCoreElaboration.Error`, `SourceCoreElaboration.ErrorSite`, `SourceCoreElaboration.WordIntegerLiteral`, `SourceCoreElaboration.NativeIntegerLiteral` |
| [`SourceCore/Lowering`](../../Solcore/Frontend/SourceCore/Lowering.lean) | `SourceCoreLocalCell.Scope`, `SourceCoreBasic.LoweredExpr`, `SourceCoreCalls.Signature`, `SourceCoreFunctions.Context` |
| [`SourceCore/Data`](../../Solcore/Frontend/SourceCore/Data.lean) | `SourceCoreDataCatalog.Catalog`, `SourceCoreDataCatalog.Error` |
| [`SourceCore/DataExpressions`](../../Solcore/Frontend/SourceCore/DataExpressions.lean) | `SourceCoreDataExpressions`, `SourceCoreGeneralTypes` |
| [`SourceCore/DataPlaces`](../../Solcore/Frontend/SourceCore/DataPlaces.lean) | `SourceCoreDataPlaces.Error`, `SourceCoreDataPlaces.declaredBinders`, `SourceCoreDataPlaces.rootBinder` |
| [`SourceCore/GeneralFunctions`](../../Solcore/Frontend/SourceCore/GeneralFunctions.lean) | `SourceCoreGeneralFunctions.Function`, `SourceCoreGeneralFunctions.CallableContext`, `SourceCoreLocalPolymorphism.Binding`, `SourceCoreStageContracts.Sidecar` |
| [`SourceCore/RawMetadata`](../../Solcore/Frontend/SourceCore/RawMetadata.lean) | `SourceCoreRawMetadata.Registry`, `SourceCoreRawMetadata.Extends` |
| [`SourceCore/CompatibleCatalog`](../../Solcore/Frontend/SourceCore/CompatibleCatalog.lean) | `SourceCoreCompatibleCatalog.Checked` |
| [`SourceCore/Compatible`](../../Solcore/Frontend/SourceCore/Compatible.lean) | `SourceCoreCompatibleValues.Context`, `SourceCoreCompatibleDataExpressions`, `SourceCoreCompatibleDataPlaces` |
| [`SourceCore/CompatibleFunctions`](../../Solcore/Frontend/SourceCore/CompatibleFunctions.lean) | `SourceCoreCompatibleFunctions`, `SourceCoreCompatibleInputs`, `SourceCoreCompatibleDataMatches` |
| [`SourceCoreUnified`](../../Solcore/Frontend/SourceCoreUnified.lean) | `SourceCoreUnifiedCompilation.Compiled` |
| [`SourceCoreCompiler`](../../Solcore/Frontend/SourceCoreCompiler.lean) | `SourceCoreCompiler.Compiled`, `SourceCoreCompiler.Error`, `SourceCoreCompiler.Options` |
| [`SourceCoreIndexedSession`](../../Solcore/Frontend/SourceCoreIndexedSession.lean) | `SourceCoreIndexedSession.Recipe`, `SourceCoreIndexedSession.Artifact`, `SourceCoreIndexedSession.Session`, `SourceCoreIndexedSession.Checkpoint` |
| [`SourceCoreLegacyHeapImport`](../../Solcore/Frontend/SourceCoreLegacyHeapImport.lean) | An explicit migration adapter |

### Theorems of the native pipeline

The source-to-Core correspondence is in `SourceSemantics/CoreLowering`, with its own page. This area
states what a successful compilation retains, in the namespace `Solcore.Frontend`:

| Result | Theorems | File |
| --- | --- | --- |
| Compilation keeps the checked source | `SourceCoreExecution.compile_checked_source`, `SourceCoreExecution.compileEntry_checked_source`, `SourceCoreExecution.compileStaticWord_checked_source` | [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) |
| The plan is validated | `SourceCoreExecution.Compiled.plan_validated` | [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) |
| Sessions stay indexed | `SourceCoreExecution.Bootstrap.ready_indexed`, `SourceCoreExecution.Session.start_indexed` | [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) |
| The runtime adapter agrees with its specialization | `SourceCoreUnifiedPreparationCertificates.run_done_specialization`, `SourceCoreUnifiedPreparationCertificates.run_resume_done_specialization` | [`SourceCoreUnified`](../../Solcore/Frontend/SourceCoreUnified.lean) |
| What checking guarantees | `checkProgram_success_method_body`, `checkProgram_success_signature_formation`, `checkProgram_success_declarations_nodup` | [`ProgramChecking`](../../Solcore/Frontend/ProgramChecking.lean) |
| Checking does not depend on the fuel | `checkProgram_success_unique_fuel` | [`ProgramChecking`](../../Solcore/Frontend/ProgramChecking.lean) |

### Internal

Checking and specialization, in `Internal/`:

| File | Topic |
| --- | --- |
| [`Internal/CheckingProperties`](../../Solcore/Frontend/Internal/CheckingProperties.lean) | What successful signature formation and trait resolution guarantee. |
| [`Internal/RuntimeValidation`](../../Solcore/Frontend/Internal/RuntimeValidation.lean) | Source heap typing, deep validation of values and heaps, and static lookup provenance. |
| [`Internal/RuntimeValues`](../../Solcore/Frontend/Internal/RuntimeValues.lean) | Source values and heap observations shared by compiler adapters, and bounded input validation. |
| [`Internal/SignatureProperties`](../../Solcore/Frontend/Internal/SignatureProperties.lean) | What successful signature collection guarantees. Its `@[simp]` lemmas, such as `ProgramFunctionSignature.parameterTypes_length`, rewrite terms that proofs in `SourceInference/Internal/ExpressionProperties` rely on, so this file stays out of their reach. |
| [`Internal/SpecializationProperties`](../../Solcore/Frontend/Internal/SpecializationProperties.lean) | What successful specialization retains, for the source semantics. |

Inference proofs, in `SourceInference/Internal/`. `ExpressionProperties` is one file of 15,543 lines
at the base, and stays one file.

| File | Topic |
| --- | --- |
| [`SourceInference/Internal/Continuations`](../../Solcore/Frontend/SourceInference/Internal/Continuations.lean) | Statement, match and `for` positions keep their inference calls and continuations. |
| [`SourceInference/Internal/DirectCallInference`](../../Solcore/Frontend/SourceInference/Internal/DirectCallInference.lean) | The inference traversals that establish those invariants. They stay apart from `DirectCallOrigins`, because each side has a private `exceptPure_eq_ok` with its own proof. |
| [`SourceInference/Internal/DirectCallOrigins`](../../Solcore/Frontend/SourceInference/Internal/DirectCallOrigins.lean) | Each direct-call requirement has an actual declaration-call emitter, and classified templates are a subset of those calls. These are the progress invariants. |
| [`SourceInference/Internal/DirectCallPredicates`](../../Solcore/Frontend/SourceInference/Internal/DirectCallPredicates.lean) | Direct-call requirements keep their raw ledger row, their catalog declaration and their exact predicate. |
| [`SourceInference/Internal/ExpressionProperties`](../../Solcore/Frontend/SourceInference/Internal/ExpressionProperties.lean) | Declaration-scoped state preservation for the inference traversals. |
| [`SourceInference/Internal/LocalGeneralization`](../../Solcore/Frontend/SourceInference/Internal/LocalGeneralization.lean) | Initialized bindings keep the inference action that generalized them, and its boundaries. |
| [`SourceInference/Internal/LocalGeneralizationBounds`](../../Solcore/Frontend/SourceInference/Internal/LocalGeneralizationBounds.lean) | The bounded event traversal of local generalization. |
| [`SourceInference/Internal/LocalReadOrigins`](../../Solcore/Frontend/SourceInference/Internal/LocalReadOrigins.lean) | Local references keep the lookup that issued their requirements, and direct-call classification follows the inference steps. |
| [`SourceInference/Internal/LocalReadScopes`](../../Solcore/Frontend/SourceInference/Internal/LocalReadScopes.lean) | Inference cannot create a reference to a retired local, and local requirements reach their initializer in time. |
| [`SourceInference/Internal/NodeGraph`](../../Solcore/Frontend/SourceInference/Internal/NodeGraph.lean) | Graph facts of the inference node table, and agreement of inference results across fuel. |
| [`SourceInference/Internal/OccurrenceProperties`](../../Solcore/Frontend/SourceInference/Internal/OccurrenceProperties.lean) | Occurrence allocation is monotone through inference. |
| [`SourceInference/Internal/ProgramProperties`](../../Solcore/Frontend/SourceInference/Internal/ProgramProperties.lean) | Success projections of source-inference finalization. |
| [`SourceInference/Internal/RequirementProperties`](../../Solcore/Frontend/SourceInference/Internal/RequirementProperties.lean) | Preservation laws for function-local obligation identities. |
| [`SourceInference/Internal/SelectedCoercionPlanTrait`](../../Solcore/Frontend/SourceInference/Internal/SelectedCoercionPlanTrait.lean) | The trait of a selected coercion plan, for the source semantics. |
| [`SourceInference/Internal/StateProperties`](../../Solcore/Frontend/SourceInference/Internal/StateProperties.lean) | Allocation and lexical restoration of the typed state. Its many `@[simp]` lemmas are why this file stays narrow. |
| [`SourceInference/Internal/TypedIRProperties`](../../Solcore/Frontend/SourceInference/Internal/TypedIRProperties.lean) | Identity preservation of final substitution over typed source. |

Lowering machinery, in `SourceCore/Internal/`:

| File | Topic |
| --- | --- |
| [`SourceCore/Internal/Allocation`](../../Solcore/Frontend/SourceCore/Internal/Allocation.lean) | Allocation markers, their discovery, fixed layouts, the source ledger and canonical contexts. |
| [`SourceCore/Internal/CallableAncestry`](../../Solcore/Frontend/SourceCore/Internal/CallableAncestry.lean) | Dynamic callable ancestry in one ordinary Core cell: programs, templates, captures, read recipes and views. |
| [`SourceCore/Internal/CallableIndexed`](../../Solcore/Frontend/SourceCore/Internal/CallableIndexed.lean) | Constant-depth ancestry over a finite table: dispatch, programs, templates, captures, views and restoration. |
| [`SourceCore/Internal/CallableOutputs`](../../Solcore/Frontend/SourceCore/Internal/CallableOutputs.lean) | Reverse source values and heap exports of the compatible, paired and indexed programs, and the public output codec. |
| [`SourceCore/Internal/CallablePaired`](../../Solcore/Frontend/SourceCore/Internal/CallablePaired.lean) | Ancestry that keeps read-time callers and lexical creators: programs, templates, captures, views and restoration. |
| [`SourceCore/Internal/CallablePrincipals`](../../Solcore/Frontend/SourceCore/Internal/CallablePrincipals.lean) | Cached principal metadata of direct lambda declarations. This file stands alone: its private instances must stay outside the closure of `Callable/CoercionSpine` in CoreLowering. |
| [`SourceCore/Internal/CallableViews`](../../Solcore/Frontend/SourceCore/Internal/CallableViews.lean) | Source views of local lambda reads, marked functions, the marked ledger and lambda templates. |
| [`SourceCore/Internal/Carriers`](../../Solcore/Frontend/SourceCore/Internal/Carriers.lean) | Heap markers and the ordinary Core frames of callable ancestry, with their decoding. These files import no source semantics, and they must not: `CallableViewWrappers` in CoreLowering has to stay outside `Solcore.SourceSemantics.Context`. |
| [`SourceCore/Internal/DirectLinking`](../../Solcore/Frontend/SourceCore/Internal/DirectLinking.lean) | Closed direct-call linking of specialized source, and the raw execution pipeline that seeds it. |
| [`SourceCore/Internal/Entries`](../../Solcore/Frontend/SourceCore/Internal/Entries.lean) | Prepared scalar, recursive, function and general entries, the catalog-backed public values, and the assignment policy. |
| [`SourceCore/Internal/FaultSites`](../../Solcore/Frontend/SourceCore/Internal/FaultSites.lean) | Source diagnostics for Core language failures: reasons, read and assignment sites, and program-wide identities. |

## Rust Hull

Read the specification first. It has no reference to Core. Then read the compiler, and then the
theorems that connect the two.

### Specification

| File | Main declarations |
| --- | --- |
| [`Syntax`](../../Solcore/Frontend/RustHull/Syntax.lean) | `Ty`, `Expr`, `Stmt`, `Function`, `YulStmt` |
| [`Decode`](../../Solcore/Frontend/RustHull/Decode.lean) | `decode`, `decodeText`, `DecodeLimits`, `DecodeError` |
| [`Semantics`](../../Solcore/Frontend/RustHull/Semantics.lean) | `Semantics.Value`, `Semantics.State`, `Semantics.Result`, `Semantics.Control`, `Semantics.EvalFunction` |
| [`Semantics/Memory`](../../Solcore/Frontend/RustHull/Semantics/Memory.lean) | `MemorySemantics.State`, `MemorySemantics.builtin`, `MemoryCopySemantics.Operation`, `MemorySnapshotSemantics` |
| [`Semantics/Digests`](../../Solcore/Frontend/RustHull/Semantics/Digests.lean) | `KeccakSemantics.Hash`, `KeccakSemantics.Builtin`, `Sha256Semantics`, `Ripemd160Semantics` |
| [`Semantics/World`](../../Solcore/Frontend/RustHull/Semantics/World.lean) | `StorageSemantics.World`, `EnvironmentSemantics.Operation`, `LogsSemantics`, `CodeImageSemantics`, `AccountObservationSemantics`, `AccountLifecycleSemantics` |
| [`Semantics/Accounts`](../../Solcore/Frontend/RustHull/Semantics/Accounts.lean) | `AccountCallSemantics.Request`, `AccountCallSemantics.Response`, `AccountCallSemantics.Shared`, `AccountCallSemantics.Mode`, `CallTransportSemantics.State` |
| [`Semantics/Layers`](../../Solcore/Frontend/RustHull/Semantics/Layers.lean) | `RuntimeEffectsSemantics.State`, `RuntimeCallEffectsSemantics.State` |
| [`Semantics/Frames`](../../Solcore/Frontend/RustHull/Semantics/Frames.lean) | `RuntimeCallModeSemantics.State`, `RuntimeCallModeSemantics.Operation`, `ChildFrameSemantics.Catalog`, `ChildFrameModeSemantics.Children`, `CreationSemantics`, `YulSemantics` |

### Compiler

The files read in dependency order. Public entry points are at the bottom.

| File | Main declarations |
| --- | --- |
| [`Memory`](../../Solcore/Frontend/RustHull/Memory.lean) | `Memory.packBytes`, `Memory.touch`, `Memory.overflowReason`, `Logs.Event` |
| [`LoweringSupport`](../../Solcore/Frontend/RustHull/LoweringSupport.lean) | `LowerM`, `LoweringError`, `Scope`, `Signature`, `Lowered`, `CodeBuilder.Code` |
| [`Precompiles`](../../Solcore/Frontend/RustHull/Precompiles.lean) | `Keccak.hash`, `Sha256.hash`, `Ripemd160.hash`, `Precompiles.staticCall` |
| [`Effects`](../../Solcore/Frontend/RustHull/Effects.lean) | `AccountState.Account`, `Effects`, `Calls`, `Creation`, `Ambient`, `CreationRuntime`, `AccountInspection`, `AccountLifecycle` |
| [`Lowering`](../../Solcore/Frontend/RustHull/Lowering.lean) | `lowerExpression`, `lowerBuiltin`, `lowerStatement`, `lowerFunction`, `assemble`, `YulLowering.lowerExpr` |
| [`CodeImage`](../../Solcore/Frontend/RustHull/CodeImage.lean) | `CodeImage.Image`, `CodeImage.resolve`, `ObjectLinking.link`, `ImageComparison` |
| [`AccountRuntime`](../../Solcore/Frontend/RustHull/AccountRuntime.lean) | `AccountRuntime.compileFrame`, `AccountRuntime.frameFunction`, `AccountRuntime.References`, `AccountRuntime.CodeDefinition`, `MemorySnapshot` |
| [`Contract`](../../Solcore/Frontend/RustHull/Contract.lean) | `Contract.compileObject`, `Contract.CompiledObject`, `Contract.Context`, `Contract.Receipt`, `Contract.Outcome` |
| [`LinkedContract`](../../Solcore/Frontend/RustHull/LinkedContract.lean) | `LinkedContract.prepare`, `LinkedContract.prepareDeployment`, `LinkedContract.compileObject` |
| [`ScalarExecution`](../../Solcore/Frontend/RustHull/ScalarExecution.lean) | `ScalarExecution.prepare`, `ScalarExecution.run`, `ScalarExecution.resume`, `ScalarExecution.Prepared` |

### Main theorems

The safety theorems assume successful preparation. They exclude Core machine faults, and leave
language failures, reverts and exhausted fuel possible.

A meaning theorem assumes more: successful compilation, syntactic eligibility, an execution that
is not a deployment, and a finite independent source evaluation. The code and call theorems add
premises about catalogs and account links. Each then relates the result, the language fault and the
source state to actual public execution, for every chain of resumptions, and states exactly how
much fuel completes it. The [Hull note](../design/hull-meaning-preservation.md) says what each one
covers.

| Result | Theorems | File |
| --- | --- | --- |
| No machine fault, scalar | `ScalarExecution.prepare_resumes_never_faults`, `ScalarExecution.prepare_resumes_hasType` | [`Safety`](../../Solcore/Frontend/RustHull/Safety.lean) |
| No machine fault, contracts | `Contract.prepare_resumes_safe`, `LinkedContract.prepare_resumes_safe` | [`Safety`](../../Solcore/Frontend/RustHull/Safety.lean) |
| Recursive programs | `Correspondence.prepare_recursive_program_resumes` | [`Correspondence`](../../Solcore/Frontend/RustHull/Correspondence.lean) |
| Ranked and pure programs | `Correspondence.prepare_ranked_program_resumes`, `Correspondence.prepare_pure_program_resumes` | [`Correspondence`](../../Solcore/Frontend/RustHull/Correspondence.lean) |
| Memory | `ContractMemoryCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Storage and transient storage | `ContractRuntimeEffectsCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Message and block observations | `ContractEnvironmentCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Logs | `ContractLogCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Explicit termination | `ContractFullCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Memory and calldata copies | `ContractCopyCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Keccak | `ContractHashCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Account observation | `ContractAccountCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Code images and catalogs | `ContractCodeCorrespondence.compileObject_resumes_exact` | [`ContractCodeTheorems`](../../Solcore/Frontend/RustHull/ContractCodeTheorems.lean) |
| Return data | `ContractReturnDataCorrespondence.compileObject_resumes_exact`, `ContractReturnDataCorrespondence.prepare_resumes_exact` | [`ContractCodeTheorems`](../../Solcore/Frontend/RustHull/ContractCodeTheorems.lean) |
| CALL and STATICCALL | `ContractCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| Compiled children | `ContractChildCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| Finite call trees | `ContractNestedChildCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| All four call modes, and account destruction | `ContractCallModeCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| Root reentry | `ContractRootCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |

The same layers have frame-level results below these, each named `compileFrame_preserves`, in
`Internal/EffectLayers`, `Internal/TerminationLayers`, `Internal/AccountLayers`,
`Internal/CallEffects` and `Internal/LinkedWorld`.

### Internal

| File | Topic |
| --- | --- |
| [`Internal/AccountCalls`](../../Solcore/Frontend/RustHull/Internal/AccountCalls.lean) | Actual account dispatch against its independent rule: checkpoints, transfers, child selection, call modes and account destruction. |
| [`Internal/AccountLayers`](../../Solcore/Frontend/RustHull/Internal/AccountLayers.lean) | The frame and message proofs of the account, code and return data layers. |
| [`Internal/CallBuiltins`](../../Solcore/Frontend/RustHull/Internal/CallBuiltins.lean) | CALL, STATICCALL, CALLCODE, DELEGATECALL, SELFDESTRUCT, revert and inline Yul through the actual builtin compiler. |
| [`Internal/CallEffects`](../../Solcore/Frontend/RustHull/Internal/CallEffects.lean) | The frame and message proofs of the call, child call and call mode layers. |
| [`Internal/CallLayout`](../../Solcore/Frontend/RustHull/Internal/CallLayout.lean) | The layout and state relation of the call layer, and the effects a call supports. It stays apart from `Internal/CallStates`: `call_fixed_separation` unfolds `Layout` millions of times, and that costs a quarter more heartbeats, past the limit, when `Layout` is declared in the same file. |
| [`Internal/CallStates`](../../Solcore/Frontend/RustHull/Internal/CallStates.lean) | The resources and updates of the call layers, and their installed callbacks. |
| [`Internal/CallTransport`](../../Solcore/Frontend/RustHull/Internal/CallTransport.lean) | Caller-frame transport and the identity precompile, with the call builtin compiler facts. |
| [`Internal/ChildFrameCalls`](../../Solcore/Frontend/RustHull/Internal/ChildFrameCalls.lean) | Finite call trees: nested children, call modes and root reentry, with their catalog links. |
| [`Internal/ChildFrames`](../../Solcore/Frontend/RustHull/Internal/ChildFrames.lean) | Fresh child frames: allocation, shared resources, invocation and completion. |
| [`Internal/Creation`](../../Solcore/Frontend/RustHull/Internal/Creation.lean) | Address derivation, preimages, handlers and transport of CREATE and CREATE2. |
| [`Internal/CreationBuiltin`](../../Solcore/Frontend/RustHull/Internal/CreationBuiltin.lean) | Actual CREATE and CREATE2 lowering against `CreationSemantics`. |
| [`Internal/Derivations`](../../Solcore/Frontend/RustHull/Internal/Derivations.lean) | Simulation by induction on a finite independent Hull derivation: atoms, expressions, calls, statements, loops, matches, faults and inline Yul. |
| [`Internal/Digests`](../../Solcore/Frontend/RustHull/Internal/Digests.lean) | The Core Keccak, SHA-256 and RIPEMD-160 against their independent definitions, block by block. |
| [`Internal/EffectBuiltins`](../../Solcore/Frontend/RustHull/Internal/EffectBuiltins.lean) | Memory, storage, log, Keccak, environment and account observation builtins through the actual builtin compiler. |
| [`Internal/EffectLayers`](../../Solcore/Frontend/RustHull/Internal/EffectLayers.lean) | The frame and message proofs of the storage, environment and log layers. |
| [`Internal/LinkedWorld`](../../Solcore/Frontend/RustHull/Internal/LinkedWorld.lean) | Exact catalog links and executable identities survive every call-free operation. |
| [`Internal/LoweringFacts`](../../Solcore/Frontend/RustHull/Internal/LoweringFacts.lean) | Shapes of the lowering output, literal parsing, scope coverage, and the exact execution of a scalar or contract receipt. |
| [`Internal/MemoryState`](../../Solcore/Frontend/RustHull/Internal/MemoryState.lean) | Core memory, range copies and logs against the independent state. |
| [`Internal/NamedFunctions`](../../Solcore/Frontend/RustHull/Internal/NamedFunctions.lean) | Function installation, parameter initialization and calls to named functions within one compiled program. |
| [`Internal/PublicFunctions`](../../Solcore/Frontend/RustHull/Internal/PublicFunctions.lean) | The public theorems for call-free and single functions, and the ranked expression interface that the program theorems use. |
| [`Internal/RuntimeFrames`](../../Solcore/Frontend/RustHull/Internal/RuntimeFrames.lean) | One compiled frame: its closures, memory initialization, completion and frame facts. |
| [`Internal/RuntimeObjects`](../../Solcore/Frontend/RustHull/Internal/RuntimeObjects.lean) | Object initialization, allocation locations, installed callbacks and the code catalog, and the first memory contract layer. |
| [`Internal/Statements`](../../Solcore/Frontend/RustHull/Internal/Statements.lean) | Operational correspondence for expressions, patterns, assignments and straight-line statements in the actual lowering output. |
| [`Internal/StorageState`](../../Solcore/Frontend/RustHull/Internal/StorageState.lean) | Core storage against the independent world, and the state relation of the effect runtime. |
| [`Internal/TerminationLayers`](../../Solcore/Frontend/RustHull/Internal/TerminationLayers.lean) | The frame and message proofs of the termination, copy and hash layers. |

## Fragments

[`Fragments`](../../Solcore/Frontend/Fragments.lean) imports the historical adapters. They are
narrow adapters from slices of the language to Core, with proofs of their own. The current pipeline
reaches none of them, apart from `WordLiteral`, and the source semantics does not use them either.
They stay because tests use them.

| File | Topic |
| --- | --- |
| [`Fragments/Internal/ClosedSource`](../../Solcore/Frontend/Fragments/Internal/ClosedSource.lean) | Closed source syntax, evaluation and executable checking. |
| [`Fragments/Internal/Computation`](../../Solcore/Frontend/Fragments/Internal/Computation.lean) | Computation bodies, return trees and compiled functions. |
| [`Fragments/Internal/Expected`](../../Solcore/Frontend/Fragments/Internal/Expected.lean) | Expected-type lambda and local binding adapters. |
| [`Fragments/Internal/ExpectedLambdas`](../../Solcore/Frontend/Fragments/Internal/ExpectedLambdas.lean) | One family of expected lambda arguments, through any depth of source groups and conditionals. |
| [`Fragments/Internal/Foundations`](../../Solcore/Frontend/Fragments/Internal/Foundations.lean) | Word binaries, word matches, named and structural types, and local references. |
| [`Fragments/Internal/LambdaDepth`](../../Solcore/Frontend/Fragments/Internal/LambdaDepth.lean) | Bounds on lambda depth in closed source, and self-application. |
| [`Fragments/Internal/LocalApplication`](../../Solcore/Frontend/Fragments/Internal/LocalApplication.lean) | Local applications and their runtime function. |
| [`Fragments/Internal/LocalComputations`](../../Solcore/Frontend/Fragments/Internal/LocalComputations.lean) | The nonrecursive union of local profiles, and its runtime function. |
| [`Fragments/Internal/LocalExpressions`](../../Solcore/Frontend/Fragments/Internal/LocalExpressions.lean) | The canonical local expression fragment: syntax, names, typing, evaluation, renaming and safety. |
| [`Fragments/Internal/LocalFunctionApplication`](../../Solcore/Frontend/Fragments/Internal/LocalFunctionApplication.lean) | Root application of a known function, with the fuel, store and resumption facts built on it. |
| [`Fragments/Internal/RecursiveComputation`](../../Solcore/Frontend/Fragments/Internal/RecursiveComputation.lean) | Recursive local computation and its entry operations. |
| [`Fragments/Internal/ReturnBodies`](../../Solcore/Frontend/Fragments/Internal/ReturnBodies.lean) | Single returns, terminal `if`, and return trees. |
| [`Fragments/Internal/RuntimeFunctions`](../../Solcore/Frontend/Fragments/Internal/RuntimeFunctions.lean) | Runtime parameter declarations and compiled runtime functions. |
| [`Fragments/Internal/RuntimeParameters`](../../Solcore/Frontend/Fragments/Internal/RuntimeParameters.lean) | Runtime parameter inputs, argument construction and input validation. |
| [`Fragments/Internal/SourceValues`](../../Solcore/Frontend/Fragments/Internal/SourceValues.lean) | Mixed values that retain source closures, with their application and matching. |
| [`Fragments/Internal/TypedLet`](../../Solcore/Frontend/Fragments/Internal/TypedLet.lean) | Annotated local declarations before a terminal return, in bodies and trees. |

## What a reviewer should know

- **The proofs about native lowering are elsewhere.** This area states what compilation retains.
  That lowered code means what the source means is in `SourceSemantics/CoreLowering`.
- **Checking sits above its proofs.** `ProgramChecking` imports `SourceInference`, whose umbrella
  imports the inference proofs, so those proofs are in the compiler's closure. The code itself
  uses none of them.
- **Some native files stay apart, and these are not choices.**
  - `SourceCore/Internal/CallablePrincipals` is alone. Its private instances rival those of
    `CallableViews`, and they have to stay outside `Callable/CoercionSpine` in CoreLowering.
  - `SourceCore/Internal/Carriers` imports no source semantics, because `CallableViewWrappers` in
    CoreLowering has to stay outside `Solcore.SourceSemantics.Context`.
  - `SourceCore/CompatibleCatalog` stays below `SourceCore/Compatible`, and
    `SourceCoreLegacyHeapImport` stays out of the public API's closure. Tests assert both with
    `#check_failure`.
  - `Internal/SignatureProperties` stays out of reach of `SourceInference/Internal/ExpressionProperties`,
    whose proofs break once `ProgramFunctionSignature.parameterTypes_length` is a `simp` lemma there.
  - `SourceCore/Data` stays below lowering. `Core.Expr.rename_weakenAt_zero` would otherwise reach
    `DataEqualityGeneration` in CoreLowering, and a `simp` argument there would become unused.
  - `ProgramSignatures` and `ProgramSignatureFormation`, `Internal/RuntimeValues` and
    `Internal/RuntimeValidation`, `SourceCore/DataExpressions` and `DataPlaces`, and
    `SourceCore/Compatible` and `CompatibleFunctions` would share matchers in one file, and
    that would rename the variables of their equation lemmas.
- **Hull is one directory with one entry.** Nothing in the native pipeline imports it. Only the
  generators reach into it, for `Keccak` and `Memory`, and `RustHull/Memory` keeps those free of
  Hull syntax.
- **Public theorems sit above frame results.** A `compileFrame_preserves` theorem is a step toward
  a contract theorem. The contract theorem is the claim, because it starts at actual compilation
  and ends at public receipts.
- **Three Hull separations are not choices either.**
  - `Logs` shares `RustHull/Memory`, below `Syntax`. It means `Core.Expr` through an `open`, and
    `RustHull.Expr` would shadow that once `Syntax` is in reach.
  - `CreationRuntime` stays in `RustHull/Effects`, below `Lowering`. It takes `boolean` from
    `CodeBuilder`, and `Lowering` declares a `boolean` of its own.
  - `Internal/CallLayout` stays apart from `Internal/CallStates`. `call_fixed_separation` unfolds
    `Layout` about 2.6 million times. Lean looks up a constant of the current file more slowly than
    an imported one, so with `Layout` in the same file the proof costs 223,663 heartbeats instead
    of 176,580, past the limit of 200,000.
