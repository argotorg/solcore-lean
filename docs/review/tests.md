# Reviewer's guide: tests

`Solcore/Test` holds the tests and their reusable fixtures. Its directories mirror the library, and
each file holds one tested feature group. `Tests/` holds `Tests/Main.lean`, which is the test driver,
the `lean_exe` roots of the case tools and scenario runners, and scripts that no target builds.

## How to run

Lean checks a test file's theorems, examples and `#check_failure` probes when it builds the file:

```bash
lake build Solcore.Test.Syntax.Yul
```

`lake build` builds every file, because `lean_lib Solcore` takes all of `Solcore.*`. The `IO` tests run
through the driver, which calls each entry point by name and ends with `solcore-lean tests passed`:

```bash
lake test
```

A full run takes about 40 minutes. Some Rust Hull groups also have a script of their own:

```bash
lake env lean --run Tests/RustHullWorldRun.lean
```

## Reading a test file

A merged file is a sequence of sections. Each starts at a line `-- leanmerge: from <old module>`, keeps
the namespace of that module, and opens with that module's own doc. `Tests/Main.lean` keeps calling the
entry points by their old names, such as `Tests.SourceArrayCases.testSourceArrayCases`.

`#check_failure` probes print an `info:` line in the build. A probe that names a constant of a module
outside the file's imports is an isolation assertion: it fails to build if a file's imports reach that
module, which is why some small groups stay apart from their neighbours.

## Which tests cover which area

### Syntax

Covers [`Solcore/Syntax`](../../Solcore/Syntax): lexer, parser, grammar correspondence.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`CanonicalTraces`](../../Solcore/Test/Syntax/CanonicalTraces.lean) | Canonical and protected trace tests | 34 |
| [`CoreBlocks`](../../Solcore/Test/Syntax/CoreBlocks.lean) | Core block tests | 21 |
| [`Declarations`](../../Solcore/Test/Syntax/Declarations.lean) | Declaration syntax tests | 68 |
| [`Diagnostics`](../../Solcore/Test/Syntax/Diagnostics.lean) | Parser diagnostics tests | 15 |
| [`ExpressionAtoms`](../../Solcore/Test/Syntax/ExpressionAtoms.lean) | Expression atom tests | 26 |
| [`ExpressionsAndPatterns`](../../Solcore/Test/Syntax/ExpressionsAndPatterns.lean) | Expression and pattern tests | 34 |
| [`LexerAndTrivia`](../../Solcore/Test/Syntax/LexerAndTrivia.lean) | Lexer, tokens and trivia tests | 25 |
| [`ModulesAndImports`](../../Solcore/Test/Syntax/ModulesAndImports.lean) | Module, import and source file tests | 57 |
| [`Parameters`](../../Solcore/Test/Syntax/Parameters.lean) | Parameter syntax tests | 21 |
| [`Pragmas`](../../Solcore/Test/Syntax/Pragmas.lean) | Pragma tests | 27 |
| [`PublicBoundary`](../../Solcore/Test/Syntax/PublicBoundary.lean) | Public parser boundary tests | 13 |
| [`Recovery`](../../Solcore/Test/Syntax/Recovery.lean) | Delimited lists, operators and recovery tests | 24 |
| [`Statements`](../../Solcore/Test/Syntax/Statements.lean) | Statement and block tests | 56 |
| [`Types`](../../Solcore/Test/Syntax/Types.lean) | Type syntax tests | 36 |
| [`Yul`](../../Solcore/Test/Syntax/Yul.lean) | Yul syntax tests | 32 |

### Core

Covers [`Solcore/Core`](../../Solcore/Core): Core semantics, typing, cells and the wire format.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`DataAndCells`](../../Solcore/Test/Core/DataAndCells.lean) | Core data and cell tests | 13 |
| [`HostMachine`](../../Solcore/Test/Core/HostMachine.lean) | Core host machine tests | 1 |
| [`LocalFragments`](../../Solcore/Test/Core/LocalFragments.lean) | Core local fragment tests | 22 |
| [`Primitives`](../../Solcore/Test/Core/Primitives.lean) | Core primitive tests | 25 |
| [`Wire`](../../Solcore/Test/Core/Wire.lean) | Core wire format tests | 6 |

### Abi

Covers [`Solcore/Abi`](../../Solcore/Abi): ABI words and the Keccak helper.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`StaticWord`](../../Solcore/Test/Abi/StaticWord.lean) | Static Word ABI tests | 11 |

### Resolved

Covers [`Solcore/Resolved`](../../Solcore/Resolved): resolved syntax and its semantics.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`Semantics`](../../Solcore/Test/Resolved/Semantics.lean) | Resolved syntax tests | 11 |

### TypeSystem

Covers [`Solcore/TypeSystem`](../../Solcore/TypeSystem): inference.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`Inference`](../../Solcore/Test/TypeSystem/Inference.lean) | Type system tests | 2 |

### ContractRuntime

Covers [`Solcore/ContractRuntime`](../../Solcore/ContractRuntime): frames, worlds, hosts, calls, creation and logs.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`AddressSelectedHost`](../../Solcore/Test/ContractRuntime/AddressSelectedHost.lean) | Address-selected host tests | 12 |
| [`ContractCalls`](../../Solcore/Test/ContractRuntime/ContractCalls.lean) | Contract call convention tests | 8 |
| [`Creation`](../../Solcore/Test/ContractRuntime/Creation.lean) | Contract creation tests | 10 |
| [`Frames`](../../Solcore/Test/ContractRuntime/Frames.lean) | Frame tests | 49 |
| [`HostDriver`](../../Solcore/Test/ContractRuntime/HostDriver.lean) | Host driver tests | 9 |
| [`Logs`](../../Solcore/Test/ContractRuntime/Logs.lean) | Log tests | 8 |
| [`NestedExecution`](../../Solcore/Test/ContractRuntime/NestedExecution.lean) | Nested execution tests | 9 |
| [`ParentIndexedFrames`](../../Solcore/Test/ContractRuntime/ParentIndexedFrames.lean) | Parent-indexed frame tests | 15 |
| [`SelectedExecution`](../../Solcore/Test/ContractRuntime/SelectedExecution.lean) | Selected execution tests | 19 |
| [`TopLevelExecution`](../../Solcore/Test/ContractRuntime/TopLevelExecution.lean) | Top-level execution tests | 15 |
| [`ValueCalls`](../../Solcore/Test/ContractRuntime/ValueCalls.lean) | Value call boundary tests | 6 |
| [`WorldState`](../../Solcore/Test/ContractRuntime/WorldState.lean) | World state tests | 19 |

### Frontend

Covers [`Solcore/Frontend`](../../Solcore/Frontend): checked programs, runtime fragments, the source compiler.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`ClosedSourceBodies`](../../Solcore/Test/Frontend/ClosedSourceBodies.lean) | Closed source body tests | 23 |
| [`ClosedSourceData`](../../Solcore/Test/Frontend/ClosedSourceData.lean) | Closed source data tests | 14 |
| [`ClosedStrictWords`](../../Solcore/Test/Frontend/ClosedStrictWords.lean) | Closed strict word tests | 13 |
| [`ComputationOwners`](../../Solcore/Test/Frontend/ComputationOwners.lean) | Computation owner tests | 25 |
| [`ComputationRuntime`](../../Solcore/Test/Frontend/ComputationRuntime.lean) | Computation runtime tests | 13 |
| [`DeepGroupedConditionals`](../../Solcore/Test/Frontend/DeepGroupedConditionals.lean) | Deep grouped conditional tests | 10 |
| [`ExpectedDataImages`](../../Solcore/Test/Frontend/ExpectedDataImages.lean) | Expected data image tests | 12 |
| [`ExpectedLambdas`](../../Solcore/Test/Frontend/ExpectedLambdas.lean) | Expected lambda tests | 22 |
| [`ExpectedPairedBridges`](../../Solcore/Test/Frontend/ExpectedPairedBridges.lean) | Expected paired bridge tests | 2 |
| [`GroupedConditionals`](../../Solcore/Test/Frontend/GroupedConditionals.lean) | Grouped conditional tests | 14 |
| [`LambdaDepth`](../../Solcore/Test/Frontend/LambdaDepth.lean) | Lambda depth tests | 18 |
| [`LocalApplicationGroups`](../../Solcore/Test/Frontend/LocalApplicationGroups.lean) | Local application wrapper tests | 22 |
| [`LocalExpressions`](../../Solcore/Test/Frontend/LocalExpressions.lean) | Local expression tests | 21 |
| [`LocalFunctions`](../../Solcore/Test/Frontend/LocalFunctions.lean) | Local function tests | 20 |
| [`MatchCounts`](../../Solcore/Test/Frontend/MatchCounts.lean) | Match tests | 22 |
| [`OwnerExpressions`](../../Solcore/Test/Frontend/OwnerExpressions.lean) | Owner expression tests | 15 |
| [`Programs`](../../Solcore/Test/Frontend/Programs.lean) | Whole program tests | 13 |
| [`PublicBoundary`](../../Solcore/Test/Frontend/PublicBoundary.lean) | Frontend public boundary tests | 2 |
| [`RecursiveComputations`](../../Solcore/Test/Frontend/RecursiveComputations.lean) | Recursive computation tests | 10 |
| [`RecursiveConditionals`](../../Solcore/Test/Frontend/RecursiveConditionals.lean) | Recursive conditional tests | 3 |
| [`RecursiveEntries`](../../Solcore/Test/Frontend/RecursiveEntries.lean) | Recursive entry tests | 15 |
| [`RecursiveFunctions`](../../Solcore/Test/Frontend/RecursiveFunctions.lean) | Recursive function tests | 2 |
| [`RecursiveLazy`](../../Solcore/Test/Frontend/RecursiveLazy.lean) | Recursive lazy tests | 4 |
| [`RecursiveRuntimeEntries`](../../Solcore/Test/Frontend/RecursiveRuntimeEntries.lean) | Recursive runtime entry tests | 2 |
| [`RecursiveTypedLetEntries`](../../Solcore/Test/Frontend/RecursiveTypedLetEntries.lean) | Recursive typed let entry tests | 2 |
| [`RecursiveUnary`](../../Solcore/Test/Frontend/RecursiveUnary.lean) | Recursive unary tests | 3 |
| [`ReturnBodies`](../../Solcore/Test/Frontend/ReturnBodies.lean) | Return body tests | 13 |
| [`RuntimeFunctions`](../../Solcore/Test/Frontend/RuntimeFunctions.lean) | Runtime function tests | 17 |
| [`RuntimeParameters`](../../Solcore/Test/Frontend/RuntimeParameters.lean) | Runtime parameter tests | 22 |
| [`RuntimeValues`](../../Solcore/Test/Frontend/RuntimeValues.lean) | Runtime value tests | 17 |
| [`Source/CompilationPlan`](../../Solcore/Test/Frontend/Source/CompilationPlan.lean) | Compilation plan tests | 2 |
| [`Source/Compiler`](../../Solcore/Test/Frontend/Source/Compiler.lean) | Source compiler tests | 15 |
| [`Source/CompilerFeatureSupport`](../../Solcore/Test/Frontend/Source/CompilerFeatureSupport.lean) | Source compiler test support | 1 |
| [`Source/Inference`](../../Solcore/Test/Frontend/Source/Inference.lean) | Source inference tests | 10 |
| [`Source/Specialization`](../../Solcore/Test/Frontend/Source/Specialization.lean) | Specialization and coercion tests | 9 |
| [`Source/Staged`](../../Solcore/Test/Frontend/Source/Staged.lean) | Staged source tests | 9 |
| [`Source/StagedIntegers`](../../Solcore/Test/Frontend/Source/StagedIntegers.lean) | Staged integer tests | 6 |
| [`Source/TypedRuntime`](../../Solcore/Test/Frontend/Source/TypedRuntime.lean) | Typed runtime tests | 4 |
| [`StructuralForms`](../../Solcore/Test/Frontend/StructuralForms.lean) | Structural form tests | 24 |
| [`SymbolicDepth`](../../Solcore/Test/Frontend/SymbolicDepth.lean) | Data depth and self-application tests | 7 |
| [`TerminalBodies`](../../Solcore/Test/Frontend/TerminalBodies.lean) | Terminal body tests | 13 |
| [`TerminalTreeInvariance`](../../Solcore/Test/Frontend/TerminalTreeInvariance.lean) | Terminal tree invariance tests | 2 |
| [`TerminalTreeRunner`](../../Solcore/Test/Frontend/TerminalTreeRunner.lean) | Terminal tree runner tests | 2 |
| [`TypedLetBodies`](../../Solcore/Test/Frontend/TypedLetBodies.lean) | Typed let body tests | 10 |
| [`TypedLetBodyRunner`](../../Solcore/Test/Frontend/TypedLetBodyRunner.lean) | Typed let body runner tests | 2 |
| [`TypedLetBodyStore`](../../Solcore/Test/Frontend/TypedLetBodyStore.lean) | Typed let body store tests | 2 |
| [`TypedLetTrees/Evaluation`](../../Solcore/Test/Frontend/TypedLetTrees/Evaluation.lean) | Typed let tree evaluation tests | 2 |
| [`TypedLetTrees/Evaluator`](../../Solcore/Test/Frontend/TypedLetTrees/Evaluator.lean) | Typed let tree evaluator tests | 2 |
| [`TypedLetTrees/Owner`](../../Solcore/Test/Frontend/TypedLetTrees/Owner.lean) | Typed let tree owner tests | 2 |
| [`TypedLetTrees/RawOwner`](../../Solcore/Test/Frontend/TypedLetTrees/RawOwner.lean) | Typed let tree raw owner tests | 2 |
| [`TypedLetTrees/Runner`](../../Solcore/Test/Frontend/TypedLetTrees/Runner.lean) | Typed let tree runner tests | 2 |
| [`TypedLetTrees/Store`](../../Solcore/Test/Frontend/TypedLetTrees/Store.lean) | Typed let tree store tests | 2 |
| [`TypedLetTrees/Trees`](../../Solcore/Test/Frontend/TypedLetTrees/Trees.lean) | Typed let tree tests | 2 |
| [`TypedLetTrees/TypeExtension`](../../Solcore/Test/Frontend/TypedLetTrees/TypeExtension.lean) | Typed let tree type extension tests | 2 |
| [`WordOperators`](../../Solcore/Test/Frontend/WordOperators.lean) | Word operator tests | 25 |

### Frontend/RustHull

Covers [`Solcore/Frontend/RustHull`](../../Solcore/Frontend/RustHull): the imported Hull: execution and correspondence with upstream.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`Accounts`](../../Solcore/Test/Frontend/RustHull/Accounts.lean) | Hull account tests | 15 |
| [`Calls`](../../Solcore/Test/Frontend/RustHull/Calls.lean) | Hull call tests | 17 |
| [`Correspondence`](../../Solcore/Test/Frontend/RustHull/Correspondence.lean) | Hull correspondence tests | 13 |
| [`Creation`](../../Solcore/Test/Frontend/RustHull/Creation.lean) | Hull creation tests | 11 |
| [`Effects`](../../Solcore/Test/Frontend/RustHull/Effects.lean) | Hull effect correspondence tests | 10 |
| [`Runtime`](../../Solcore/Test/Frontend/RustHull/Runtime.lean) | Hull runtime tests | 8 |

### SourceSemantics

Covers [`Solcore/SourceSemantics`](../../Solcore/SourceSemantics): source semantics and inference.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`CompiledOrigins`](../../Solcore/Test/SourceSemantics/CompiledOrigins.lean) | Compiled origin tests | 22 |
| [`Inference`](../../Solcore/Test/SourceSemantics/Inference.lean) | Source inference tests | 6 |
| [`Semantics`](../../Solcore/Test/SourceSemantics/Semantics.lean) | Source semantics tests | 9 |
| [`SemanticsBoundary`](../../Solcore/Test/SourceSemantics/SemanticsBoundary.lean) | Source semantics boundary tests | 3 |
| [`SemanticsSubstitution`](../../Solcore/Test/SourceSemantics/SemanticsSubstitution.lean) | Source substitution tests | 1 |

### SourceSemantics/CoreLowering

Covers [`Solcore/SourceSemantics/CoreLowering`](../../Solcore/SourceSemantics/CoreLowering): source to Core: fixtures, compiled programs, public execution.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`Builtin`](../../Solcore/Test/SourceSemantics/CoreLowering/Builtin.lean) | Builtin lowering tests | 25 |
| [`Callable/Ancestry`](../../Solcore/Test/SourceSemantics/CoreLowering/Callable/Ancestry.lean) | Callable ancestry tests | 24 |
| [`Callable/Coercion`](../../Solcore/Test/SourceSemantics/CoreLowering/Callable/Coercion.lean) | Callable coercion tests | 18 |
| [`Callable/Indexed`](../../Solcore/Test/SourceSemantics/CoreLowering/Callable/Indexed.lean) | Indexed callable tests | 23 |
| [`Callable/IndexedLambda`](../../Solcore/Test/SourceSemantics/CoreLowering/Callable/IndexedLambda.lean) | Indexed lambda tests | 22 |
| [`Callable/LambdaViews`](../../Solcore/Test/SourceSemantics/CoreLowering/Callable/LambdaViews.lean) | Lambda view tests | 14 |
| [`Callable/Paired`](../../Solcore/Test/SourceSemantics/CoreLowering/Callable/Paired.lean) | Paired callable tests | 22 |
| [`Callable/Prepared`](../../Solcore/Test/SourceSemantics/CoreLowering/Callable/Prepared.lean) | Prepared callable tests | 12 |
| [`Canonical/Formation`](../../Solcore/Test/SourceSemantics/CoreLowering/Canonical/Formation.lean) | Canonical formation tests | 18 |
| [`Canonical/Scoped`](../../Solcore/Test/SourceSemantics/CoreLowering/Canonical/Scoped.lean) | Canonical scoped tests | 26 |
| [`Captured/Assignments`](../../Solcore/Test/SourceSemantics/CoreLowering/Captured/Assignments.lean) | Captured closure assignment tests | 36 |
| [`Captured/Branches`](../../Solcore/Test/SourceSemantics/CoreLowering/Captured/Branches.lean) | Captured closure branch tests | 26 |
| [`Captured/Locals`](../../Solcore/Test/SourceSemantics/CoreLowering/Captured/Locals.lean) | Captured local tests | 28 |
| [`Captured/Loops`](../../Solcore/Test/SourceSemantics/CoreLowering/Captured/Loops.lean) | Captured closure loop tests | 26 |
| [`Captured/Mappings`](../../Solcore/Test/SourceSemantics/CoreLowering/Captured/Mappings.lean) | Captured mapping tests | 14 |
| [`Captured/Nested`](../../Solcore/Test/SourceSemantics/CoreLowering/Captured/Nested.lean) | Nested capture tests | 19 |
| [`Chosen/Admission`](../../Solcore/Test/SourceSemantics/CoreLowering/Chosen/Admission.lean) | Chosen ordinary admission tests | 18 |
| [`Chosen/Bodies`](../../Solcore/Test/SourceSemantics/CoreLowering/Chosen/Bodies.lean) | Chosen ordinary body tests | 16 |
| [`Chosen/OuterBodies`](../../Solcore/Test/SourceSemantics/CoreLowering/Chosen/OuterBodies.lean) | Chosen ordinary outer body tests | 9 |
| [`Chosen/PublicOutcomes`](../../Solcore/Test/SourceSemantics/CoreLowering/Chosen/PublicOutcomes.lean) | Chosen ordinary public tests | 9 |
| [`Closed/Admitted`](../../Solcore/Test/SourceSemantics/CoreLowering/Closed/Admitted.lean) | Closed admitted tests | 5 |
| [`Closed/Owned`](../../Solcore/Test/SourceSemantics/CoreLowering/Closed/Owned.lean) | Closed owned tests | 14 |
| [`ClosureDirect`](../../Solcore/Test/SourceSemantics/CoreLowering/ClosureDirect.lean) | Direct closure tests | 17 |
| [`CoercionPublic`](../../Solcore/Test/SourceSemantics/CoreLowering/CoercionPublic.lean) | Public coercion tests | 26 |
| [`Compatible/Ambient`](../../Solcore/Test/SourceSemantics/CoreLowering/Compatible/Ambient.lean) | Compatible ambient tests | 17 |
| [`Compatible/Encoding`](../../Solcore/Test/SourceSemantics/CoreLowering/Compatible/Encoding.lean) | Compatible encoding tests | 5 |
| [`Compatible/Expressions`](../../Solcore/Test/SourceSemantics/CoreLowering/Compatible/Expressions.lean) | Compatible expression tests | 15 |
| [`Compatible/General`](../../Solcore/Test/SourceSemantics/CoreLowering/Compatible/General.lean) | Compatible general tests | 20 |
| [`Compatible/Matches`](../../Solcore/Test/SourceSemantics/CoreLowering/Compatible/Matches.lean) | Compatible match tests | 15 |
| [`Compatible/Payloads`](../../Solcore/Test/SourceSemantics/CoreLowering/Compatible/Payloads.lean) | Compatible payload tests | 2 |
| [`Compatible/Statements`](../../Solcore/Test/SourceSemantics/CoreLowering/Compatible/Statements.lean) | Compatible statement tests | 14 |
| [`Constructor`](../../Solcore/Test/SourceSemantics/CoreLowering/Constructor.lean) | Constructor call tests | 22 |
| [`Data/Places`](../../Solcore/Test/SourceSemantics/CoreLowering/Data/Places.lean) | Data place tests | 21 |
| [`Data/Values`](../../Solcore/Test/SourceSemantics/CoreLowering/Data/Values.lean) | Data value tests | 18 |
| [`Direct/Calls`](../../Solcore/Test/SourceSemantics/CoreLowering/Direct/Calls.lean) | Direct call tests | 32 |
| [`Direct/Linking`](../../Solcore/Test/SourceSemantics/CoreLowering/Direct/Linking.lean) | Direct linking tests | 1 |
| [`Evidence/Closure`](../../Solcore/Test/SourceSemantics/CoreLowering/Evidence/Closure.lean) | Closure evidence tests | 20 |
| [`Evidence/Direct`](../../Solcore/Test/SourceSemantics/CoreLowering/Evidence/Direct.lean) | Direct evidence tests | 16 |
| [`Evidence/Method`](../../Solcore/Test/SourceSemantics/CoreLowering/Evidence/Method.lean) | Method evidence tests | 16 |
| [`Evidence/Scoped`](../../Solcore/Test/SourceSemantics/CoreLowering/Evidence/Scoped.lean) | Scoped evidence tests | 18 |
| [`Foundations/EntryPoints`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/EntryPoints.lean) | Lowering entry point tests | 20 |
| [`Foundations/Execution`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean) | Lowering execution tests | 25 |
| [`Foundations/Heaps`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Heaps.lean) | Heap and allocation tests | 18 |
| [`Foundations/ReachableDiagnostics`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/ReachableDiagnostics.lean) | Reachable statement tests | 19 |
| [`Foundations/Snapshots`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Snapshots.lean) | Snapshot tests | 2 |
| [`Foundations/Stages`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Stages.lean) | Stage contract tests | 3 |
| [`Foundations/Statements`](../../Solcore/Test/SourceSemantics/CoreLowering/Foundations/Statements.lean) | Basic statement tests | 37 |
| [`Generalized/Body`](../../Solcore/Test/SourceSemantics/CoreLowering/Generalized/Body.lean) | Generalized body tests | 28 |
| [`Generalized/Export`](../../Solcore/Test/SourceSemantics/CoreLowering/Generalized/Export.lean) | Generalized export tests | 34 |
| [`GenericDirect`](../../Solcore/Test/SourceSemantics/CoreLowering/GenericDirect.lean) | Generic direct call tests | 16 |
| [`LexicalFailure`](../../Solcore/Test/SourceSemantics/CoreLowering/LexicalFailure.lean) | Lexical failure tests | 25 |
| [`LexicalFailureForward`](../../Solcore/Test/SourceSemantics/CoreLowering/LexicalFailureForward.lean) | Lexical failure forward tests | 8 |
| [`Method/Closure`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/Closure.lean) | Method closure tests | 20 |
| [`Method/DirectEvidence`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/DirectEvidence.lean) | Direct method evidence tests | 23 |
| [`Method/GenericSubstitution`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/GenericSubstitution.lean) | Generic substitution tests | 23 |
| [`Method/ImplementationScoped`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/ImplementationScoped.lean) | Implementation-scoped method tests | 23 |
| [`Method/NamedScoped`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/NamedScoped.lean) | Named scoped method tests | 22 |
| [`Method/OriginEvidence`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/OriginEvidence.lean) | Method origin evidence tests | 32 |
| [`Method/OriginFixture`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/OriginFixture.lean) | Method origin fixture tests | 16 |
| [`Method/OwnEvidence`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/OwnEvidence.lean) | Own method evidence tests | 23 |
| [`Method/PublicSequences`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/PublicSequences.lean) | Method public sequence tests | 24 |
| [`Method/Scoped`](../../Solcore/Test/SourceSemantics/CoreLowering/Method/Scoped.lean) | Scoped method tests | 21 |
| [`Mixed/Control`](../../Solcore/Test/SourceSemantics/CoreLowering/Mixed/Control.lean) | Mixed control tests | 29 |
| [`Mixed/Loops`](../../Solcore/Test/SourceSemantics/CoreLowering/Mixed/Loops.lean) | Mixed loop tests | 28 |
| [`Mixed/Operators`](../../Solcore/Test/SourceSemantics/CoreLowering/Mixed/Operators.lean) | Mixed operator tests | 31 |
| [`Mixed/Reads`](../../Solcore/Test/SourceSemantics/CoreLowering/Mixed/Reads.lean) | Mixed read tests | 30 |
| [`Named/Branches`](../../Solcore/Test/SourceSemantics/CoreLowering/Named/Branches.lean) | Named branch tests | 36 |
| [`Named/Loops`](../../Solcore/Test/SourceSemantics/CoreLowering/Named/Loops.lean) | Named loop tests | 26 |
| [`Named/Operators`](../../Solcore/Test/SourceSemantics/CoreLowering/Named/Operators.lean) | Named operator tests | 17 |
| [`NestedFormation`](../../Solcore/Test/SourceSemantics/CoreLowering/NestedFormation.lean) | Nested formation tests | 20 |
| [`OperatorCalls`](../../Solcore/Test/SourceSemantics/CoreLowering/OperatorCalls.lean) | Operator call tests | 13 |
| [`Protected`](../../Solcore/Test/SourceSemantics/CoreLowering/Protected.lean) | Protected statement tests | 14 |
| [`Recursive/Formation`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/Formation.lean) | Recursive formation tests | 19 |
| [`Recursive/Index`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/Index.lean) | Recursive index tests | 27 |
| [`Recursive/NamedCatalog`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/NamedCatalog.lean) | Recursive named catalog tests | 20 |
| [`Recursive/NamedExpressions`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/NamedExpressions.lean) | Recursive named expression tests | 15 |
| [`Recursive/NamedHeaders`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/NamedHeaders.lean) | Recursive named header tests | 21 |
| [`Recursive/NamedPublic`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/NamedPublic.lean) | Recursive named public tests | 18 |
| [`Recursive/NamedStatements`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/NamedStatements.lean) | Recursive named statement tests | 13 |
| [`Recursive/Stages`](../../Solcore/Test/SourceSemantics/CoreLowering/Recursive/Stages.lean) | Recursive stage tests | 9 |
| [`Selected/Faulting`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/Faulting.lean) | Faulting selected tests | 23 |
| [`Selected/Generalized`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/Generalized.lean) | Generalized selected tests | 29 |
| [`Selected/GeneralizedSource`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/GeneralizedSource.lean) | Generalized local source tests | 2 |
| [`Selected/Interleaved`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/Interleaved.lean) | Interleaved selected tests | 12 |
| [`Selected/OperatorAlias`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/OperatorAlias.lean) | Selected operator alias tests | 1 |
| [`Selected/Profiles`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/Profiles.lean) | Selected profile tests | 22 |
| [`Selected/ProfilesControl`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/ProfilesControl.lean) | Selected control profile tests | 11 |
| [`Selected/Projected`](../../Solcore/Test/SourceSemantics/CoreLowering/Selected/Projected.lean) | Selected projected tests | 17 |
| [`TypedStatements`](../../Solcore/Test/SourceSemantics/CoreLowering/TypedStatements.lean) | Typed statement tests | 17 |
| [`UnifiedCorpus`](../../Solcore/Test/SourceSemantics/CoreLowering/UnifiedCorpus.lean) | Unified corpus tests | 8 |
| [`UnifiedCorpusSupport`](../../Solcore/Test/SourceSemantics/CoreLowering/UnifiedCorpusSupport.lean) | Unified corpus test support | 1 |
| [`UnifiedOperatorCorpus`](../../Solcore/Test/SourceSemantics/CoreLowering/UnifiedOperatorCorpus.lean) | Unified operator corpus tests | 1 |

### Synthesis

Covers [`Solcore/Synthesis`](../../Solcore/Synthesis): generators, emitters, golden files and fixed corpora.

| File | Tests | Old modules |
| --- | --- | ---: |
| [`Aggregates`](../../Solcore/Test/Synthesis/Aggregates.lean) | Aggregate and closure profile tests | 9 |
| [`Arrays`](../../Solcore/Test/Synthesis/Arrays.lean) | Array profile tests | 10 |
| [`Bytes`](../../Solcore/Test/Synthesis/Bytes.lean) | Bytes profile tests | 12 |
| [`CallGraphs`](../../Solcore/Test/Synthesis/CallGraphs.lean) | Call graph profile tests | 10 |
| [`Calls`](../../Solcore/Test/Synthesis/Calls.lean) | Call profile tests | 17 |
| [`Enums`](../../Solcore/Test/Synthesis/Enums.lean) | Enum profile tests | 10 |
| [`EventsAndReverts`](../../Solcore/Test/Synthesis/EventsAndReverts.lean) | Event and revert profile tests | 4 |
| [`Generators`](../../Solcore/Test/Synthesis/Generators.lean) | Generator tests | 18 |
| [`Loops`](../../Solcore/Test/Synthesis/Loops.lean) | Loop profile tests | 18 |
| [`Malformed`](../../Solcore/Test/Synthesis/Malformed.lean) | Malformed calldata profile tests | 9 |
| [`Memory`](../../Solcore/Test/Synthesis/Memory.lean) | Memory profile tests | 2 |
| [`Scalars`](../../Solcore/Test/Synthesis/Scalars.lean) | Scalar profile tests | 16 |
| [`SourceMeaning`](../../Solcore/Test/Synthesis/SourceMeaning.lean) | Source meaning tests | 10 |
| [`Storage`](../../Solcore/Test/Synthesis/Storage.lean) | Storage profile tests | 16 |
| [`Traits`](../../Solcore/Test/Synthesis/Traits.lean) | Trait profile tests | 5 |

## Why some files are small

A few neighbouring groups cannot share a file, because a merge would change a declaration. Each split
runs along a feature of its own:

- **Recursive helpers.** A definition by well-founded recursion has a compiled twin, `f._unsafe_rec`, that
  names itself, so renaming a differing private copy changes the twin. Each feature of typed let trees has
  its own `certify`, so the features are separate files in `Frontend/TypedLetTrees`. The same holds for
  `TypedLetBodyRunner`, `TypedLetBodyStore`, `TerminalTreeInvariance`, `TerminalTreeRunner`,
  `RecursiveRuntimeEntries` and `RecursiveTypedLetEntries`.
- **Matchers.** Inside a file Lean reuses a matcher even when its bound names differ, and the equations
  `f.eq_i` take their variable names from it. This keeps `RecursiveFunctions`, `RecursiveConditionals`,
  `RecursiveLazy`, `RecursiveUnary` and `SymbolicDepth` apart from their neighbours.
- **Binder annotations.** Lean also reuses an auxiliary whose binders differ only in annotations. This
  keeps `ExpectedPairedBridges` apart from `ExpectedDataImages`, and is why `Selected/OperatorAlias`,
  `Selected/GeneralizedSource`, `Foundations/Snapshots` and `Chosen/OuterBodies` are files of their own.

Two more splits keep public names of a test out of a neighbour's reach. `LexicalFailureForward` keeps the
names of the initial failure namespace from `Selected/Faulting`, which opens that namespace, and
`UnifiedOperatorCorpus` keeps the public `Compiled` of the unified compilation tests from `Callable/Prepared`.

## A file that stays where it is

[`Solcore/Test/SourceCallReturnGolden.lean`](../../Solcore/Test/SourceCallReturnGolden.lean) keeps its path
and stays alone. `scripts/test-semantic-call-differential.py` reads it by path and scans it with a regex
for its golden rows, so it can neither move nor share a file with other tuples of strings.
