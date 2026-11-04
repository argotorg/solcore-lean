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
| [`Source/CompilationPlan`](../../Solcore/Test/Frontend/Source/CompilationPlan.lean) | Compilation plan tests | 2 |
| [`Source/Compiler`](../../Solcore/Test/Frontend/Source/Compiler.lean) | Source compiler tests | 15 |
| [`Source/CompilerFeatureSupport`](../../Solcore/Test/Frontend/Source/CompilerFeatureSupport.lean) | Source compiler test support | 1 |
| [`Source/Inference`](../../Solcore/Test/Frontend/Source/Inference.lean) | Source inference tests | 10 |
| [`Source/Specialization`](../../Solcore/Test/Frontend/Source/Specialization.lean) | Specialization and coercion tests | 9 |
| [`Source/Staged`](../../Solcore/Test/Frontend/Source/Staged.lean) | Staged source tests | 9 |
| [`Source/StagedIntegers`](../../Solcore/Test/Frontend/Source/StagedIntegers.lean) | Staged integer tests | 6 |
| [`Source/TypedRuntime`](../../Solcore/Test/Frontend/Source/TypedRuntime.lean) | Typed runtime tests | 4 |

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

## A file that stays where it is

[`Solcore/Test/SourceCallReturnGolden.lean`](../../Solcore/Test/SourceCallReturnGolden.lean) keeps its path
and stays alone. `scripts/test-semantic-call-differential.py` reads it by path and scans it with a regex
for its golden rows, so it can neither move nor share a file with other tuples of strings.

## Not merged yet

2205 old modules are still flat in `Solcore/Test`.
