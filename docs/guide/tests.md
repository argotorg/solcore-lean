# Tests

`Solcore/Test/` holds the tests and their shared fixtures, by subject, in directories that mirror
the library. `Tests/` holds the test driver [`Tests/Main.lean`](../../Tests/Main.lean), the
executables of the differential tests, focused runners, fixtures and the corpus validators. Each
area's page lists the tests that cover it; this page says how tests are written, registered, run
and compared.

## Kinds of test

- **Checks that run when a file builds.** `example`s and `theorem`s proved by `decide`, `rfl`,
  `simp` or `native_decide`, and `#check_failure` probes. Building the file runs them.
- **IO tests.** A `def … : IO Unit` that throws `IO.userError` when a check fails, usually through
  a private helper of its section (`assertTrue`, `check`, `ensure`, `require`, `get`). Only the
  driver, or a focused runner, runs them.
- **Golden and corpus tests** are IO tests whose expected values are written in the file or read
  from a fixed corpus; see [Expected values](#expected-values).

A merged test file is a sequence of sections. Each starts at a line
`-- leanmerge: from <old module>` and keeps that module's namespace, such as
`Tests.SourceArrayCases`.

## Where things are

### `Solcore/Test/`

| Directory | Area page | Files |
| --- | --- | --- |
| [`Syntax/`](../../Solcore/Test/Syntax) | [Syntax](syntax.md): lexer, parser, diagnostics, traces | `CanonicalTraces`, `CoreBlocks`, `Declarations`, `Diagnostics`, `ExpressionAtoms`, `ExpressionsAndPatterns`, `LexerAndTrivia`, `ModulesAndImports`, `Parameters`, `Pragmas`, `PublicBoundary`, `Recovery`, `Statements`, `Types`, `Yul` |
| [`Core/`](../../Solcore/Test/Core) | [Core](core.md): semantics, typing, cells, the wire format | `DataAndCells`, `HostMachine`, `LocalFragments`, `Primitives`, `Wire` |
| [`Abi/`](../../Solcore/Test/Abi), [`Resolved/`](../../Solcore/Test/Resolved), [`TypeSystem/`](../../Solcore/Test/TypeSystem) | [Foundations](foundations.md): ABI words, resolved syntax, inference | `Abi/StaticWord`, `Resolved/Semantics`, `TypeSystem/Inference` |
| [`ContractRuntime/`](../../Solcore/Test/ContractRuntime) | [ContractRuntime](contract-runtime.md): frames, worlds, hosts, calls, creation, logs | `AddressSelectedHost`, `ContractCalls`, `Creation`, `Frames`, `HostDriver`, `Logs`, `NestedExecution`, `ParentIndexedFrames`, `SelectedExecution`, `TopLevelExecution`, `ValueCalls`, `WorldState` |
| [`Frontend/`](../../Solcore/Test/Frontend) | [Frontend](frontend.md): checked programs and runtime fragments | `ClosedSourceBodies`, `ClosedSourceData`, `ClosedStrictWords`, `ComputationOwners`, `ComputationRuntime`, `DeepGroupedConditionals`, `ExpectedDataImages`, `ExpectedLambdas`, `ExpectedPairedBridges`, `GroupedConditionals`, `LambdaDepth`, `LocalApplicationGroups`, `LocalExpressions`, `LocalFunctions`, `MatchCounts`, `OwnerExpressions`, `Programs`, `PublicBoundary`, `RecursiveComputations`, `RecursiveConditionals`, `RecursiveEntries`, `RecursiveFunctions`, `RecursiveLazy`, `RecursiveRuntimeEntries`, `RecursiveTypedLetEntries`, `RecursiveUnary`, `ReturnBodies`, `RuntimeFunctions`, `RuntimeParameters`, `RuntimeValues`, `StructuralForms`, `SymbolicDepth`, `TerminalBodies`, `TerminalTreeInvariance`, `TerminalTreeRunner`, `TypedLetBodies`, `TypedLetBodyRunner`, `TypedLetBodyStore`, `WordOperators` |
| [`Frontend/TypedLetTrees/`](../../Solcore/Test/Frontend/TypedLetTrees) | [Frontend](frontend.md): typed let trees | `Evaluation`, `Evaluator`, `Owner`, `RawOwner`, `Runner`, `Store`, `Trees`, `TypeExtension` |
| [`Frontend/Source/`](../../Solcore/Test/Frontend/Source) | [Frontend](frontend.md): the native compiler | `CompilationPlan`, `Compiler`, `CompilerFeatureSupport` (a shared fixture), `Inference`, `Specialization`, `Staged`, `StagedIntegers`, `TypedRuntime` |
| [`Frontend/RustHull/`](../../Solcore/Test/Frontend/RustHull) | [Frontend](frontend.md): the imported Hull, its execution and its correspondence with upstream | `Accounts`, `Calls`, `Correspondence`, `Creation`, `Effects`, `Runtime`, `YulPrimitives` |
| [`SourceSemantics/`](../../Solcore/Test/SourceSemantics) | [Source semantics](source-semantics.md): the semantics and inference | `CompiledOrigins`, `Inference`, `IntegerBitNot`, `Semantics`, `SemanticsBoundary`, `SemanticsSubstitution` |
| [`SourceSemantics/CoreLowering/`](../../Solcore/Test/SourceSemantics/CoreLowering) | [Core lowering](core-lowering.md): fixtures, compiled programs, public execution | The table below |
| [`Synthesis/`](../../Solcore/Test/Synthesis) | [Synthesis](synthesis.md#testing): generators, emitters, golden rows, fixed corpora | `Aggregates`, `Arrays`, `Bytes`, `CallGraphs`, `Calls`, `Captures`, `Enums`, `EventsAndReverts`, `Generators`, `Loops`, `Malformed`, `Memory`, `Scalars`, `SourceMeaning`, `Storage`, `Traits` |
| [`SourceCallReturnGolden.lean`](../../Solcore/Test/SourceCallReturnGolden.lean) | [Synthesis](synthesis.md#testing) | Stays at the top level; see [Pitfalls](#pitfalls) |

`SourceSemantics/CoreLowering/`:

| Subdirectory | Files |
| --- | --- |
| (top level) | `Builtin`, `ClosureDirect`, `CoercionPublic`, `Constructor`, `GenericDirect`, `LexicalFailure`, `LexicalFailureForward`, `NestedFormation`, `OperatorCalls`, `Protected`, `TypedStatements`, `UnifiedCorpus`, `UnifiedCorpusSupport` (a shared fixture), `UnifiedOperatorCorpus` |
| `Callable/` | `Ancestry`, `Coercion`, `Indexed`, `IndexedLambda`, `LambdaViews`, `Paired`, `Prepared` |
| `Canonical/` | `Formation`, `Scoped` |
| `Captured/` | `Assignments`, `Branches`, `Locals`, `Loops`, `Mappings`, `Nested` |
| `Chosen/` | `Admission`, `Bodies`, `OuterBodies`, `PublicOutcomes` |
| `Closed/` | `Admitted`, `Owned` |
| `Compatible/` | `Ambient`, `Encoding`, `Expressions`, `General`, `Matches`, `Payloads`, `Statements` |
| `Data/` | `Places`, `Values` |
| `Direct/` | `Calls`, `Linking` |
| `Evidence/` | `Closure`, `Direct`, `Method`, `Scoped` |
| `Foundations/` | `EntryPoints`, `Execution`, `Heaps`, `ReachableDiagnostics`, `Snapshots`, `Stages`, `Statements` |
| `Generalized/` | `Body`, `Export` |
| `Method/` | `Closure`, `DirectEvidence`, `GenericSubstitution`, `ImplementationScoped`, `NamedScoped`, `OriginEvidence`, `OriginFixture`, `OwnEvidence`, `PublicSequences`, `Scoped` |
| `Mixed/` | `Control`, `Loops`, `Operators`, `Reads` |
| `Named/` | `Branches`, `Loops`, `Operators` |
| `Recursive/` | `Formation`, `Index`, `NamedCatalog`, `NamedExpressions`, `NamedHeaders`, `NamedPublic`, `NamedStatements`, `Stages` |
| `Selected/` | `Faulting`, `Generalized`, `GeneralizedSource`, `Interleaved`, `OperatorAlias`, `Profiles`, `ProfilesControl`, `Projected` |

### `Tests/`

| Path | What it is | How it runs |
| --- | --- | --- |
| [`Main.lean`](../../Tests/Main.lean) | The test driver. A few older tests are defined in it. | `lake test` (`lean_exe solcoreTests`, executable `solcore-tests`) |
| `Semantic*Tool.lean` | The case tools of the synthesis profiles: `SemanticCaseTool` for every pure profile, one tool per stateful profile; see [Synthesis](synthesis.md#profiles) | One `lean_exe` each in [`lakefile.lean`](../../lakefile.lean) |
| `RustHullContractRun.lean`, `RustHull*ScenarioRun.lean` | The imported-Hull runners of the differential tests | One `lean_exe` each (`rust-hull-*`) |
| The other `RustHull*Run.lean`, `RustHull*Profile.lean`, `RustParity.lean` | Scripts with a `main`. Some run one group of driver tests: `RustHullKeccakRun.lean` is `def main : IO Unit := Tests.RustHullKeccak.run`. `scripts/rust-*-parity.py` and `scripts/test-rust-opcode-wrappers.py` run others. | `lake env lean --run Tests/<File>.lean`; no target builds them |
| [`Fixtures/`](../../Tests/Fixtures) | Inputs of scripts: the EVM account reference (`EvmAccounts/`, for `scripts/evm-account-reference.py`; the Hull creation tests repeat its address vectors) and Solidity sources for `scripts/test-rust-opcode-wrappers.py` and `scripts/test-rust-recursive-layouts.py` | — |
| [`scripts/`](../../Tests/scripts) | The corpus validators `test-semantic-*-corpus.py` and `test-semantic-chunked-generation.py`, which run the native case tools and no EVM | `python3 Tests/scripts/<file>` |

Every executable other than the driver is also listed in `TARGETS` of
`scripts/prepare-semantic-tools.py`, which prepares them for the differential tests; a new one goes
in both places.

## The driver

`Tests/Main.lean` imports the test files and calls their IO entry points, in `main` and in the
groups `main` calls (`Tests.run`, `Tests.staticSemanticsSpineTests`). It takes no arguments and
runs everything. The first failing check throws, which stops the run with its message; at the end
it prints `solcore-lean tests passed` and returns 0.

The entry points keep the namespaces of the modules they came from:
`Tests.SourceArrayCases.testSourceArrayCases` is in `Solcore/Test/Synthesis/Arrays.lean`. To find
one, search for its namespace or for the marker `-- leanmerge: from Solcore.Test.SourceArrayCases`.

## Adding a test

1. **Pick the file** by subject from the tables above, or from the area's page. Create a file only
   when no subject fits.
2. **Add a section** at the end of the file: `section`, a module doc that says what the tests check,
   `set_option autoImplicit false` as in the other sections, and a namespace of its own, such as
   `namespace Tests.SourceFooCases`. Do not add a `-- leanmerge:` marker.
3. **Write the checks.**
   - A check that runs at build time is an `example` or a `theorem`, usually by `decide`, `rfl` or
     `simp`.
   - An IO test is a `def testFoo : IO Unit`, with the section's own private helpers that throw
     `IO.userError`.
   - Use an independent source for expected values; see [Expected values](#expected-values).
4. **Register it** in `Tests/Main.lean`: `import` the file if it is new, and call the entry point
   from `main` or from `Tests.run`. Every test file is reachable from the driver's imports today;
   keep it so.
5. **Build the file, then run the driver:** `lake build Solcore.Test.<Dir>.<File>`, then
   `lake test`.

In `6b2f86b99`, for example, a cases test of two synthesis profiles took one import and one call
in the driver; since the layout refactor it is the section `Tests.SourceIntegerCases` of
`Solcore/Test/Synthesis/Scalars.lean`.

## Running tests

```sh
lake build Solcore.Test.Syntax.Yul                  # one file: its examples, theorems and probes
lake build                                          # every module under Solcore/, tests included
lake test                                           # builds and runs the driver: every IO test
lake env lean --run Tests/RustHullWorldRun.lean     # one group of driver tests, through its runner
python3 Tests/scripts/test-semantic-shift-corpus.py # one corpus validator
```

- `lake build` builds every test file, because the library's glob is `Solcore.*`. `lake test`
  builds only what the driver imports.
- A full `lake test` takes about half an hour: the gates recorded in the
  [roadmap](../design/next-implementation-roadmap.md) give 28 to 40 minutes.
- There is no option to run part of the driver. To run one group, use a focused runner of the shape
  above. `lake env` builds nothing, so build the test module it imports first: for
  `RustHullWorldRun.lean`, `lake build Solcore.Test.Frontend.RustHull.Accounts`.
- The corpus validators run the tools in `.lake/build/bin/` by default, `semantic-case-tool` for
  the pure profiles; build them first, for example with `lake build semanticCaseTool`.
- Run the driver from the repository root: the corpus tests and the P256 vectors are read from
  `scripts/` by relative paths.
- CI runs `lake build` and `lake test` after the kernel check and the Python tests;
  [Workflow](workflow.md#before-you-commit) lists the commands.

## `native_decide`

Tests may decide a concrete fixture with `native_decide`, as `Abi/StaticWord`, several
ContractRuntime tests and `Synthesis/Generators` do. Library code may not: see
[Conventions](conventions.md#proof-rules). The kernel check does not look for `native_decide`, and
it does not visit `Solcore/Test` or `Tests` at all, so tests may also use `partial`, as some Syntax
tests do.

## Expected values

- **No expected-output files.** Tests compare values in Lean. Some print progress lines, but
  nothing compares what the driver prints. A `#check_failure` probe's message in the build output
  is expected.
- **Golden tests** write the expected source text or rows in the test file. The values come from a
  model independent of the code under test, such as a Python model, `cast`, or fixed boundary Words.
  For example, `Tests.SourceCallBranchGolden` says its rows come from an independent Python model,
  and the primitive corpus test says its expected Words are "never compiler output". When a
  deliberate change moves a golden value, take the new value from the independent model.
- **Corpus tests** read a fixed corpus, `scripts/semantic-*-corpus.json`, and check each entry
  against a fresh Core run. The Python validators in `Tests/scripts/` check other corpora with
  fresh runs of the native tools; some also re-emit each source and compare it exactly.

## Pitfalls

- **Warnings are errors.** The package sets `warningAsError`, so an unused variable fails the test
  file's build.
- **A built test is not a run test.** A new file is compiled by `lake build` whether or not the
  driver imports it, but its IO tests run only once `Tests/Main.lean` calls them.
- **`private` is per file.** Two sections that declare a private helper of the same name in the
  same namespace clash; a namespace of its own avoids that.
- **Shared fixtures.** `Frontend/Source/CompilerFeatureSupport` and
  `SourceSemantics/CoreLowering/UnifiedCorpusSupport` are imported by many test files, and other
  test files import each other. Check the importers before you change a helper.
- **Isolation probes.** A `#check_failure` that names a constant of a module outside the file's
  imports asserts that the file does not reach that module; `Frontend/Source/CompilationPlan`
  checks that compilation preparation imports neither evaluator. A new import that reaches the
  module makes the probe succeed, and the build fails.
- **Some files must stay apart,** because merging them would change a declaration:
  - **Recursive helpers.** A definition by well-founded recursion has a compiled twin,
    `f._unsafe_rec`, that names itself, so renaming a differing private copy changes the twin. Each
    feature of typed let trees has its own `certify`, so the features are separate files in
    `Frontend/TypedLetTrees`; so are `TypedLetBodyRunner`, `TypedLetBodyStore`,
    `TerminalTreeInvariance`, `TerminalTreeRunner`, `RecursiveRuntimeEntries` and
    `RecursiveTypedLetEntries`.
  - **Matchers.** Within a file Lean reuses a matcher even when its bound names differ, and the
    equations `f.eq_i` take their variable names from it. This keeps `RecursiveFunctions`,
    `RecursiveConditionals`, `RecursiveLazy`, `RecursiveUnary` and `SymbolicDepth` apart.
  - **Binder annotations.** Lean also reuses an auxiliary whose binders differ only in
    annotations. This keeps `ExpectedPairedBridges` apart from `ExpectedDataImages`, and
    `Selected/OperatorAlias`, `Selected/GeneralizedSource`, `Foundations/Snapshots` and
    `Chosen/OuterBodies` in files of their own.
  - **Names in reach.** `LexicalFailureForward` keeps the names it adds to the namespace
    `Tests.SourceCoreInitialLexicalFailure` out of `Selected/Faulting`, which opens that namespace.
    `UnifiedOperatorCorpus` keeps the public `Compiled` of the unified compilation tests from
    `Callable/Prepared`.
- **`SourceCallReturnGolden.lean` stays where it is.** `scripts/test-semantic-call-differential.py`
  reads it by path and takes its golden rows with a regular expression, so keep each row in the form
  `("…", "…", "0x…", "…")`, and keep other four-string tuples out of the file.
