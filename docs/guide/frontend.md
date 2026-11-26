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
  `SourceInference/TypedIR`, and [core lowering](core-lowering.md) over the actual compiler
  functions. The generators of [Synthesis](synthesis.md) import `RustHull/Precompiles` for Keccak.
  The tests and README use the public APIs.

## Where things are

### Native pipeline

A program flows down this table. `checkProgram` loads it (validating the workspace, parsing each
file through `Syntax/Unchecked`, building the declaration environment), resolves imports, types and
signatures, and checks every function and method body. `Syntax/Unchecked` also reads a `let`'s
top-level `comptime<T>` annotation as `T`, and the compilation plan requires that binder to be
comptime-staged (`comptimeLetStageMismatch`). In the modules reachable from the entry,
the load refuses the imports that upstream refuses where they are (`programImportErrors`): a name
brought beside a declaration of the module, an unknown item, a name listed twice, a name brought
from two modules, a qualifier beside a value of that name, two imports under one qualifier, and
an unknown module other than one of upstream's std modules. It refuses there two functions of
one name in a module (`duplicateFunctionErrors`, upstream's `SC0108`), so a call names one
function; a function and a type of one name stay apart. It refuses there too the exports
upstream refuses: a local export that names nothing the module declares or a selected or
wildcard import brings, a constructor that its type does not show, a re-export that its module
does not show, std's modules by their export tables, one public name for items of two origins,
a std name's by the std module that declares it, and one public name for two modules. A
module's names resolve through the modules it reaches
(`buildProgramInterfacesFrom`), so an error in a module that nothing imports refuses no
program. An import of `std.opcodes` binds upstream's 81 names, of which the 26
pure functions are builtins (`builtinNamed?`), and `!` and `<` call the `not` and `lt` that it
binds, as upstream's do (`operatorBuiltin?`). A plain import qualifies them by `opcodes` and
`std.opcodes`, and a namespace import by its alias (`qualifiedBuiltinNamed?`). A std name that
a user module re-exports binds on through its importers, `std.opcodes`' functions to their
builtins (`ProgramPublicStandard`). A qualified name in a value names what it names in a
call: a function of an imported module, the reference its unqualified name gives, or one of
those builtins (`qualifiedValueReference?`). A plain import of a nested path names its module
by its last component and by the full path it is seen by, a leading `lib` and an external
library's name dropped (`ProgramImportedNamespace.path`). Upstream's
primitive `primAddWord` is the builtin word addition wherever no local, declaration or import
takes the name, since upstream's builtin terms come last in its lookup
(`builtinFunctionNamed?`). Upstream's builtin `sum<a, b>`, with `inl` and `inr`, is one data
type of a standard module that the load adds where a workspace file names it
(`builtinSumSource`). No import names that module; its type and its unqualified constructor
calls come after a module's own and imported names, and its constructors are visible in every
module (`builtinTypesNamed`, `builtinSumDataTypes`). An import of
another std module binds no name and is checked by the names that the module exports
(`upstreamStandardModuleExports`). `SourceCoreCompiler.compileChecked` then
plans the specializations of the requested roots, validates the plan, and compiles one cached Core
artifact. `SourceCoreExecution.prepare` turns that artifact into the recipe that sessions run.

| File | Holds |
| --- | --- |
| **Public API** | |
| [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean) | Re-exports `SourceCoreExecution`; add a public name to its `export` lists |
| [`SourceCoreExecution`](../../Solcore/Frontend/SourceCoreExecution.lean) | `compile`, `compileChecked`, `compileEntry`, `compileStaticWord`, `Compiled`, `Artifact`, `Session`, `Checkpoint`, `Outcome` |
| [`Current`](../../Solcore/Frontend/Current.lean) | Imports every stage of the pipeline; declares nothing |
| **Loading and checking** | |
| [`WordLiteral`](../../Solcore/Frontend/WordLiteral.lean) | `NumericLiteralDenotes`, `numericLiteralValue?`, `WordLiteralDenotes`, `interpretWordLiteral?`; for a negative literal, `NegativeLiteralDenotes` and `literalMagnitude?` |
| [`ProgramInterfaces`](../../Solcore/Frontend/ProgramInterfaces.lean) | Identities, the declaration catalog `ProgramEnvironment`, interfaces, and loading: `loadProgram`, `ProgramLoadError` |
| [`ProgramImports`](../../Solcore/Frontend/ProgramImports.lean) | `ProgramImports`, `buildProgramImports`, `ProgramImportError` |
| [`StandardModules`](../../Solcore/Frontend/StandardModules.lean) | Upstream's std modules at the pin: their paths, `std.opcodes`' functions and each other module's exported names with their namespaces, each export's origin and the constructors a std type shows; generated by `scripts/standard-modules.py` |
| [`ProgramTypeResolution`](../../Solcore/Frontend/ProgramTypeResolution.lean) | `ProgramTypeScope`, `validateProgramTypeScope`, `ProgramTypeResolutionError`; `resolveNamedProgramType`, which takes a module's own types, then its imports', then the builtins `word`, `bool` and the twelve fixed-width types (`builtinTypeName?`), so `Word`, `Bool`, `Unit` and `unit` name nothing (`SC0103`) |
| [`ProgramSignatures`](../../Solcore/Frontend/ProgramSignatures.lean) | `ProgramFunctionSignature`, `ProgramPredicate`, `ProgramSignatures`; `builtinFunctionNamed?`, which finds a builtin closure by its spelling and then a conversion by its type's name; `superclassClosure`, which closes a body's givens under their superclasses, `reachedByTwoGivens`, and `impliedConditions`, an impl's conditions with its head's unstated superclasses; the checks of each impl where it is declared: an impl method's results compared with its trait method's as one tuple (`validateRequiredImplMethods`) and recorded in the trait method's instantiated shape (`attachTraitMethods`), the orphan rule (`SC0246`), overlapping defaults (`SC0247`), the overlap check of ordinary impls (`SC0218`, `overlappingImplementationErrors`), which compares a program's own `Coerce` (`isConventionalCoerce`) on both arguments (`ordinaryHeadsOverlap`), and a default's subject, the coverage condition and the Patterson condition (`SC0219`, `SC0212`, `SC0213`, `implementationConditionErrors`), the last two lifted by its module's `pragma no-coverage-condition` or `no-patterson-condition`, for every trait or for the traits it names, and an implementation of `Shl` or `Shr` at `word` or a fixed-width type, which Lean's shifts never take (`shiftImplementationErrors`); the closure under superclasses of each function's and impl's `where` predicates, and of each trait and impl method's, with the lists as written in `declaredPredicates` and `declaredWherePredicates` |
| [`ProgramSignatureFormation`](../../Solcore/Frontend/ProgramSignatureFormation.lean) | `ProgramSignatureFormationValidated`, `ProgramSignatureFormationError` |
| [`TraitResolution`](../../Solcore/Frontend/TraitResolution.lean) | The tabled trait search and its typed instance: `TraitResolution.Evidence`, `TypedTraitResolution.Evidence`. A goal equal to a given is decided by it first (`Program.givens`), and a non-default head that can describe the goal blocks the defaults (`Program.blocksDefaults`) |
| [`SourceInference/TypedIR`](../../Solcore/Frontend/SourceInference/TypedIR.lean) | The typed IR: `TypedSource`, `ExpressionNode`, `ExpressionForm`, `TypedBinder`, and a match's written scrutinees (`MatchResolution.parts`) |
| [`SourceInference/Types`](../../Solcore/Frontend/SourceInference/Types.lean) | `State`, `Context`, `CheckedFunction`, `SolvedRequirement`, `Error` |
| [`SourceInference/Resolution`](../../Solcore/Frontend/SourceInference/Resolution.lean) | Operator, overload and trait selection: `binaryOperatorDispatch`, `inferBinaryOperator`, `withExpected`; an operator's trait, the one declared with the operator's name under any name a scope gives it (`operatorTrait?`, `declaredTraitCandidates`); the builtin operators at the twelve fixed-width types (`fixedBinaryOperator`); operands that wait for their type (`binaryDefers`); the types of compound and in-place `~` targets (`compoundOperandType`, `bitNotTargetType`, `bitNotTargetFits`); what a qualified value names (`qualifiedValueReference?`) |
| [`SourceInference/Expression`](../../Solcore/Frontend/SourceInference/Expression.lean) | The traversal `inferExprFuel`, `inferStatementFuel`, `inferStatementsFuel`, with the shift and unchecked branches, a qualified call's `Typedef` branch (`typedefCall?`, `typedefFunction`), a constructor pattern's `uint256(p)` branch (`uint256PatternArgument?`), a binder pattern's `true` and `false`, which name the booleans (`MatchPatternResolution.boolLiteral`), its same-name constructor with the refusal of another constructor's spelling (`sameNameConstructorVisible`, `constructorLeafVisible`), a constructor pattern's unqualified head (`constructorHeadQualifiers`, `unqualifiedConstructorRefused`), and an identifier's last reading, the constructor that shares its type's name (`constructorCalleeCandidates`), after locals, functions and builtins, as a call of the name reads it after a function or a builtin (`functionOrBuiltinNamed`), a leading dot's `.true` and `.false` as the booleans where the expected type is `bool` (`leadingDotBoolean?`), and a match's coverage beside its catch-all and nominal checks (`coverageSplit?`, `rowsCoverFuel`, `coversMatchCases`) |
| [`SourceInference/Program`](../../Solcore/Frontend/SourceInference/Program.lean) | `checkFunctionBody`, which first refuses a statement after a `return` in its sequence (`nonFinalReturnInStatements`), and `finalize`. `finalize` first fixes each requirement's open trait arguments from the one given, ordinary impl or default whose head matches its closed subject, as upstream's `match_pred` does (`Detail.fixWeakArguments`), leaving a program's own `Coerce` to the coercion search, and does so again after the numeric defaulting (`Detail.defaultTargets`). It defaults an open numeric pattern to `uint256`, and an open literal where one of the uses that `Detail.literalDefaultsToUint256` lists takes it, rejecting it as ambiguous elsewhere. It checks literal ranges (`Detail.signedLiteralFitsTarget`), and runs the checks that wait for final types: assignment targets, unchecked, shift and array operands, array literals and element places (`Detail.validateAssignmentTargets`, `Detail.validateUncheckedOperand`, `Detail.validateShiftOperands`, `Detail.validateArrayIndex`, `Detail.validateArrayLiteral`, `Detail.validatePlaceElements`). It then refuses an operator that took its builtin at `word` or a fixed-width type beside an implementation of the operator's trait there, the trait taken by the name the scope sees it under (`Detail.validateBuiltinOperatorUses`). `inferExpression`, whose own type stays open, leaves a lone open literal ambiguous where upstream's root rule gives it `uint256` |
| [`SourceInference`](../../Solcore/Frontend/SourceInference.lean) | The inference umbrella, which also imports five of its proof files |
| [`ProgramChecking`](../../Solcore/Frontend/ProgramChecking.lean) | `checkProgram`, `CheckedProgram`, `ProgramCheckError`; `missingSuperclassErrors`, upstream's `SC0248`, before the bodies, and `ambiguousGivenErrors`, its `SC0208` for a goal that two givens reach, after them |
| **Staging and specialization** | |
| [`SourceStageAnalysis`](../../Solcore/Frontend/SourceStageAnalysis.lean) | `SourceStageAnalysis.analyzeFunction`, `Stage`, and the staged values `SourceStagedValue.Value`; a match's written scrutinees are classified with their tuple and give each arm's binders their stages (`Detail.analyzeMatchScrutineeWith`, `Detail.registerArmBinders`) |
| [`SourceSpecialization`](../../Solcore/Frontend/SourceSpecialization.lean) | `SpecializationKey`, `SpecializedFunction` |
| [`SourceSpecializationWorklist`](../../Solcore/Frontend/SourceSpecializationWorklist.lean) | `SourceSpecializationWorklist.run`, `Plan`, `Request` |
| [`ExecutableImplMethods`](../../Solcore/Frontend/ExecutableImplMethods.lean) | `ExecutableImplMethods.CheckedMethod` |
| [`SourceCompilationPlan`](../../Solcore/Frontend/SourceCompilationPlan.lean) | `exactSpecialization`, `exactInstantiationKey`, `validateExecutablePlanEvidence` |
| **Elaboration and lowering** | |
| [`SourceCoreElaboration`](../../Solcore/Frontend/SourceCoreElaboration.lean) | Literal evidence, with the range checked again at a fixed-width integer type (`validateFixedIntegerLiteral`, `validateNegativeFixedIntegerLiteral`), closed types, elaboration errors; Core operators for source operators |
| [`SourceCore/Lowering`](../../Solcore/Frontend/SourceCore/Lowering.lean) | Scalars, locals, control, loops, assignments, calls and function values, by section: `SourceCorePrimitive`, `SourceCoreAssignments`, `SourceCoreSourceCells`, `SourceCoreFunctions` and others |
| [`SourceCore/Data`](../../Solcore/Frontend/SourceCore/Data.lean) | `SourceCoreDataCatalog.Catalog`: closed data, equality and defaults |
| [`SourceCore/DataExpressions`](../../Solcore/Frontend/SourceCore/DataExpressions.lean), [`DataPlaces`](../../Solcore/Frontend/SourceCore/DataPlaces.lean) | Data leaves, and places as Core getters and updaters (`SourceCoreDataPlaces.lower`) |
| [`SourceCore/GeneralFunctions`](../../Solcore/Frontend/SourceCore/GeneralFunctions.lean) | Matches, evidence, local polymorphism, staging contracts, general functions |
| [`SourceCore/RawMetadata`](../../Solcore/Frontend/SourceCore/RawMetadata.lean) | `SourceCoreRawMetadata.Registry` |
| [`SourceCore/RootTypes`](../../Solcore/Frontend/SourceCore/RootTypes.lean) | `SourceCoreRootTypes.holdsView`: whether a type holds a memory array, a slice or a memref, also through the payloads of the enums it names; `ViewFree` and its laws for the proofs |
| [`SourceCore/CompatibleCatalog`](../../Solcore/Frontend/SourceCore/CompatibleCatalog.lean), [`Compatible`](../../Solcore/Frontend/SourceCore/Compatible.lean), [`CompatibleFunctions`](../../Solcore/Frontend/SourceCore/CompatibleFunctions.lean) | The source-compatible profile: catalog, values, data leaves and places, patterns, inputs, functions |
| [`SourceCoreUnified`](../../Solcore/Frontend/SourceCoreUnified.lean) | `SourceCoreUnifiedCompilation.Compiled`, the one cached artifact, and its runtime adapter |
| [`SourceCoreCompiler`](../../Solcore/Frontend/SourceCoreCompiler.lean) | `compileChecked`, `compile`, `Options`, `Error`, for an ordered root set. `compileChecked` rejects a root whose parameter or result type holds a memory array, a slice or a memref (`Error.rootWithoutPublicValue`) |
| [`SourceCoreIndexedSession`](../../Solcore/Frontend/SourceCoreIndexedSession.lean) | `Recipe`, `Artifact`, `Session`, `Checkpoint`: persistent typed Core sessions. A session refuses to prepare a root, and to call a handle, whose type holds a memory array, a slice or a memref (`ErrorCode.rootWithoutPublicValue`, `ErrorCode.handleWithoutPublicValue`) |
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
| [`SourceCore/Internal/FaultSites`](../../Solcore/Frontend/SourceCore/Internal/FaultSites.lean) | Source diagnostics for Core language failures, such as the sites of an assignment's operands (`SourceCoreAssignmentFaultSites.operandTarget`) |

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
`checkProgram_success_unique_fuel` or `Bootstrap.ready_indexed`. The Hull note says what each
meaning theorem assumes and what remains: the elliptic-curve precompiles, creation with init frames,
more of inline Yul, and object linking.

## Making changes

### A new construct in the native compiler

[Adding a language feature](adding-a-feature.md) follows the shifts through every layer. The
compiler's steps:

1. **Syntax**, as [Syntax](syntax.md#making-changes) describes. A pass around the parser also needs
   `parseWorkspaceFile` in `ProgramInterfaces`, and a `ProgramLoadError` for its failures, as the
   `pragma solcore;` check after the parse has (`pragmaSolcoreProblems`).
2. **Typed IR.** A new operator needs none: `ExpressionForm` carries `Syntax.BinaryOp` and
   `Syntax.ValueAssignOp`. A new form needs a constructor in `SourceInference/TypedIR`.
3. **Inference**, in `SourceInference/Resolution`: the dispatch (`binaryOperatorDispatch`) and the
   typing rule (`inferBinaryOperator`, whose shift branch runs before any dispatch). A compound
   form that takes a fixed-width target's type also needs its case in `compoundOperandConstructor`
   and `compoundTakesTargetType`. What is still open waits for its type (a compound target, a
   literal operand, a shift's value and amount, a compound shift's amount), and finalization checks
   it in `SourceInference/Program` (`compoundTargetFits`, `validateUncheckedOperand`,
   `validateShiftOperands`, `validateShiftAmount`).
4. **Its arm.** A new form needs its arm in `inferExprFuel` (`SourceInference/Expression`). A form
   that inference only rejects shares the last arm until a later step gives it a meaning; the last
   arm now keeps only the parser's recovery nodes. `new T[](n)` and the slices each took their arm
   in a commit of its own, which only renumbered the proofs' cases, before the commit that typed
   them.
5. **Inference proofs**: the new branch's lemmas next to it, as `inferBinaryOperator_shift_result`
   is, then every case analysis in `SourceInference/Internal/ExpressionProperties`.
6. **Elaboration and lowering**: the Core operator in `SourceCoreElaboration` (`directBinary`), and
   the operator's cases in `SourceCore/Lowering` (`SourceCorePrimitive.strictBinaryBody`,
   `SourceCoreAssignments.operator?`), and in the operator tables and guards of
   `SourceCoreDataPlaces.lower` and `SourceCore/Compatible`.
7. **Fragments and frontend tests**: their exhaustive matches, in `Fragments/Internal/` and in tests
   such as `ClosedStrictWords`.
8. **Semantics and proofs**: the [source semantics](source-semantics.md) and
   [core lowering](core-lowering.md). A new guard in the lowering becomes a premise there: since the
   data-place lowering refuses Word-only operators at `integer` leaves, the shared assignment
   premise reads `operator.wordOnly = false`.
9. **Tests**: a public-API test with a `run`, called from `Tests/Main.lean`, such as
   `Tests.SourceCoreShiftExecution`, with the expected values of the pinned Rust paths and the
   programs that must be rejected.

### A change to what an existing construct compiles to

Closures by value are the example ([Core lowering](core-lowering.md#closures-by-value)). Put a
decision that the semantics and the lowering both make in one function, low in the imports:
`CaptureBinders.copiedBinder?` in `SourceSemantics/CaptureBinders` imports only
`SourceInference/TypedIR`. Change the lowering (here `SourceCoreSourceCells`, `SourceCoreFunctions`
and `SourceCoreLoops` in `SourceCore/Lowering`) and the semantics together, and expect to restate
the core lowering theorems that describe the old code and the tests' expected results.

### A new public entry point

Define it in `SourceCoreExecution` and add it to the `export` lists of `SourceCompiler`.
`UnifiedCorpus` in `Solcore/Test/SourceSemantics/CoreLowering` checks the exports with `rfl`, and
`#check_failure` probes there and in `Source/Compiler` assert names that must stay absent.

### Rust Hull: executable support for a builtin or construct

1. A new node in the export: `RustHull/Syntax` and `RustHull/Decode`. The decoder rejects unknown
   fields, another schema and another upstream revision.
2. The compiler: `RustHull/Lowering` and `LoweringSupport`, the effect builtins in
   `RustHull/Effects`, frames in `AccountRuntime`, code images in `CodeImage`, and the boundaries in
   `Contract` and `LinkedContract`.
3. `RustHull/Safety` must still prove the safety theorems for the new code.
4. Tests in `Solcore/Test/Frontend/RustHull/`, with fixtures under `Tests/Fixtures/`, and a runner
   or script when Rust output is compared, as `Tests/RustHullOpcodeWrappersRun.lean` and
   `scripts/test-rust-opcode-wrappers.py` are for the opcode wrappers.

### Rust Hull: connecting a feature to the meaning theorems

1. The independent rule: for Yul, `YulSemantics` in `Semantics/Frames`; for a precompile, its
   digest in `Semantics/Digests` and its dispatch in `Semantics/Accounts`.
2. The simulation in `RustHull/Internal/`: `Derivations` and `CallBuiltins` for Yul; `Digests` and
   `CallTransport` for a precompile.
3. The public theorem of the layer, and a consumer of it in the tests, such as those in
   `Solcore/Test/Frontend/RustHull/Effects`.
4. The status tables of the Hull note. Its completion rule: a feature is connected only when its
   independent derivation reaches the actual compiler and the public run and resume API.

### Rust Hull: an exporter change or a new pin

- In Lean: `RustHull.upstreamCommit`, `CodeImage.backendRevision` when the backend moves, the
  revision named in `RustHull/Lowering`'s inline-Yul section, and the sample export in
  `Solcore/Test/Frontend/RustHull/Effects`. Grep for the old revision. Raise `DecodeLimits` if
  exports grow.
- `Solcore/Frontend/StandardModules.lean`: `scripts/standard-modules.py --write` regenerates it
  from the new pin's `std`, and its test checks it against the checkout.
- Outside Lean: the exporters and manifests; see [Differential testing](differential-testing.md)
  and [`scripts/RUST_PARITY.md`](../../scripts/RUST_PARITY.md). Moving the pin is a change of its
  own.

## Pitfalls

- **Core lowering reads the compiler's code.** Its proofs unfold compiler definitions and state
  premises in their terms, so a change to a compiler function is a change to those proofs. Plan it
  with the [core lowering](core-lowering.md) work.
- **Inference proofs number their cases.** They do functional induction on `inferExprFuel` and name
  its cases by number, in `SourceInference/Internal` and `SourceSemantics/Internal`. A new arm, or a
  new syntax constructor it matches on, shifts them; a constructor that only reaches the last arm,
  as the parser's recovery nodes do, shifts nothing. This is why `unchecked` is a pass around the
  parser. Pattern proofs do the same with `inferMatchPatternFlatFuel.induct`.
- **The compiler imports the inference proofs.** `ProgramChecking` imports the `SourceInference`
  umbrella, which imports five proof files, so a broken inference proof stops the compiler build.
- **Files kept apart on purpose:**
  - `SourceCore/Internal/CallablePrincipals` stands alone: its private instances, which
    `CallableViews` also declares, must stay outside the closure of core lowering's
    `Callable/CoercionSpine`.
  - `SourceCore/Internal/Carriers` imports no source semantics, so that core lowering's
    `CallableViewWrappers` stays outside `Solcore.SourceSemantics.Context`.
  - `SourceCore/Data` stays below the lowering: core lowering imports it, and a wider closure
    changes its `simp` calls.
  - `Internal/SignatureProperties` stays out of reach of `ExpressionProperties`, whose proofs break
    once `ProgramFunctionSignature.parameterTypes_length` is a `simp` lemma there.
  - `DirectCallInference` and `DirectCallOrigins` each have a private `exceptPure_eq_ok` with its
    own proof.
  - These pairs would share matchers in one file, which renames the variables of their equation
    lemmas: `ProgramSignatures` and `ProgramSignatureFormation`, `Internal/RuntimeValues` and
    `RuntimeValidation`, `DataExpressions` and `DataPlaces`, `Compatible` and
    `CompatibleFunctions`.
- **Tests assert imports.** `#check_failure` probes keep `SourceCore/CompatibleCatalog` below the
  value encoder of `SourceCore/Compatible` (`Compatible/Payloads`) and `SourceCoreLegacyHeapImport`
  out of the public API (`UnifiedCorpus`). A new import can break them.
- **Hull files kept apart on purpose:**
  - `RustHull/Memory`, which holds `Logs`, and `RustHull/Precompiles` import no Hull syntax: the
    generators import `Precompiles`, and under `open Core` their `Expr` means `Core.Expr`, which
    `RustHull.Expr` would make ambiguous. The test file `RustHull/YulPrimitives` stays apart from
    `RustHull/Runtime` for the same reason.
  - `CreationRuntime` stays in `RustHull/Effects`, below `Lowering`: it uses `CodeBuilder.boolean`,
    and `Lowering` declares a `boolean` of its own.
  - `Internal/CallLayout` stays apart from `Internal/CallStates`: `call_fixed_separation` unfolds
    `Layout` so often that it passes the heartbeat limit when `Layout` is in the same file.
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

Some Hull runners are executables of their own, such as `rustHullScenario`
(`lake build rustHullScenario`); others run as scripts, such as
`lake env lean --run Tests/RustHullWorldRun.lean`. [Tests](tests.md) says how the tests are
organized.
