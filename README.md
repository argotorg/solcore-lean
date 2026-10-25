# solcore-lean

An executable specification of Solcore in Lean 4.

The project includes a source frontend, a typed intermediate language (Core),
and a model of contract execution. Source programs compile to Core. The Core
machine runs with an execution-step budget and can resume from a checkpoint.
The contract runtime models accounts, storage, calls, and transaction commits
and rollbacks.

## Build and test

Use Lean and Lake with the version pinned in [lean-toolchain](lean-toolchain).
From the repository root:

```sh
lake build
lake test
node scripts/check-kernel.mjs
```

Node.js is needed for the kernel check. Lean warnings are treated as errors.

## Using the frontend

The compiler is a Lean library. Import its public API with:

```lean
import Solcore.Frontend.SourceCompiler
```

A small source program:

```text
function main() returns (Word) {
  return 55;
}
```

Source files are supplied as a `Workspace.RawWorkspace`. The
[execution tests](Solcore/Test/SourceCoreExecution.lean) show how to compile a
workspace, open a session, call an entry point, and resume after the fuel runs
out. They also cover recursive functions, closures with mutable captures, and
mappings. See the [API guide](docs/design/core-runtime-unification-api.md) for
values, handles, snapshots, and execution options.

## Running solcore-rs output

The [Rust Hull importer](Solcore/Frontend/RustHull/) accepts typed output from
`argotorg/solcore-rs` at commit `2a745e12974c373c3799fec81b48a53c7dce2ab4`.
It checks the imported annotations, translates Hull and inline Yul into Core,
and checks the resulting Core expression before execution.

This path supports all 81 standard opcode wrappers, contract constructors,
dynamic ABI values, byte memory, storage, logs, and calls between imported
accounts. CREATE/CREATE2 and SELFDESTRUCT update an explicit account world.
Keccak, SHA-256, RIPEMD-160, ECRECOVER and P256 verification execute in Core.
Exact linked Sonatina code images supply observable code bytes and object
offsets; execution uses the Core machine.

The export scripts require a checkout of the pinned Rust revision. They patch
only the isolated checkout supplied to `--upstream` and record source and tool
hashes beside each artifact. Run each script with `--help` for build and path
options:

- [export-rust-hull.py](scripts/export-rust-hull.py): checked Hull transport.
- [export-rust-code-image.py](scripts/export-rust-code-image.py): linked code images.
- [rust-scenario-parity.py](scripts/rust-scenario-parity.py): constructor and
  stateful execution against upstream fixture expectations.

Import the library with `import Solcore.Frontend.RustHull`. The entry points are
`RustHull.decodeText`, `RustHull.ScalarExecution.prepare`,
`RustHull.LinkedContract.prepareDeployment` and `RustHull.Contract.runWithReceipt`.
[RustHullScenarioRun.lean](Tests/RustHullScenarioRun.lean) shows artifact loading,
deployment, account balances and sequential calls. A context supplies account
state, transaction/block observations, and an optional gas value. Executable
code comes from a checked Hull catalogue with exact linked images. Core fuel
counts transitions; EVM gas consumption is not metered.

The pinned contract inventory covers 168 fixtures. The checked Rust driver
accepts 165; their 1,382 constructor and call observations match the fixture
expectations on Core. Three fixtures fail upstream source checks before export.
[RUST_PARITY.md](scripts/RUST_PARITY.md) lists the gates and how to reproduce them.
The Rust EVM reference runs separately through Sonatina at O0 and O2 and through
Yul compiled by solc. These checks compare each execution with fixture
expectations; they do not yet compare arbitrary generated programs directly.

Importing Rust Hull does not prove the Rust compiler correct or extend the
native Lean source checker to every Rust feature. Recursive references use the
Rust backends’ Word layout; aggregate construction and unfolding cases that fail
in both backends remain explicit errors. Arbitrary EVM bytecode and additional
precompiles are outside the executable code catalogue. The compatibility gates
and their limits are documented in [RUST_PARITY.md](scripts/RUST_PARITY.md).

## Proof status

Core has proofs of type preservation and finite execution safety. The
independent source semantics also has a type preservation proof. Correspondence
between native source execution and generated Core code has been proved for
parts of the language; the theorem covering the complete compiler remains
unfinished. The [Core runtime unification design](docs/design/core-runtime-unification.md)
records that work.

`import Solcore.Frontend.RustHull.Safety` provides safety proofs for imported
Hull. Successful preparation supplies the typing conditions for input parsing,
contract initialization, execution and checkpoint resumption. These proofs
exclude Core machine faults while allowing language failures, reverts and
exhausted fuel budgets.

The separate [Hull meaning-preservation proofs](docs/design/hull-meaning-preservation.md)
connect independent finite Hull evaluations to actual lowering and public
execution, including repeated resumptions. Connected features include recursive
functions, loops, language faults, memory, storage, logs, return data, all four
message-call modes, root reentry and account destruction. Contract creation,
precompile execution, independent assembly semantics and object linking still
need their full public meaning-preservation connections. Executable support is
broader than this proved subset.

The native source compiler handles closed entry points with a finite
specialization plan. Its source contract members, persistent storage and
external calls have yet to be connected to `ContractRuntime`; its ABI wrapper
is limited to static Word values. The Rust Hull path has a separate import
boundary and supports generated dynamic ABI code.

## Differential testing

Semantic differential testing against the pinned Rust compiler runs a small,
gas-independent subset. It does not require completion of every remaining Hull
correspondence proof.

[Synthesis.Core](Solcore/Synthesis/Core.lean) already provides deterministic
generation and shrinking of pure Word programs with Boolean subexpressions,
local bindings, conditionals and primitive operations. Generated and reduced
programs pass the Core checker; accepted programs carry a proof of Core typing.
The [source emitter](Solcore/Synthesis/Source/Emitter.lean) renders a restricted
subset as a fixed Solcore contract. A native case tool records seeds and
versions, rechecks saved inputs and recomputes the original Core result.
Emitter regressions include actual checked Rust compilation and imported-Hull
execution. Core typing does not establish the emitter's meaning preservation.

The [differential-testing milestones](docs/design/semantic-differential-testing.md)
specify source emission, seed replay, failure classification and reduction. A
single-case runner compares the original generated Core result, Rust-produced
EVM execution, and execution of Rust Hull on Lean Core. It saves all three
observations and verifies tools and artifact hashes during replay. A campaign
runner reduces failures while preserving their classification and disagreeing
paths, with explicit time, disk and attempt limits. The fixed sixteen-case
corpus covers the enabled source operations and boundary values; all sixteen
cases match across the three execution paths. Core fuel, EVM gas and process
timeouts remain separate resource limits.
See [generated semantic comparisons](scripts/SEMANTIC_DIFFERENTIAL.md) for the
tools, supported operations and validation commands. Closed generated programs
may be constant-folded; source coverage is not runtime opcode coverage.

A separate runtime-input profile applies checked Word-to-Word functions to
recorded ABI inputs. Identity and input-dependent branch cases agree across all
three paths at zero, one, maximum Word and the high bit, with identical source
for each function's inputs. A further profile supports one to three acyclic
named helpers, including shared callees, with checked generation and reduction
of the complete Core function graph. The local-mutation profile compares private
Word cells, ordered reads and writes, Unit sequencing, and helper-local state.
Its fixed 28-case corpus matches across all three paths, including cases where
a read must retain its value before a later write. The aggregate profile adds
internal Word pairs and sums, projections and matches, mixed with mutable locals
and helper calls. All 32 fixed aggregate cases agree across the three paths.
The ABI and helper arguments/results remain Word-only. Bounded loops use an
actual source `while` and an independently executed finite Core reference, with
up to seven iterations. All 48 fixed loop cases match across the three paths.
M1 through M4 are complete for these restricted profiles.

The first stateful profile compares one to three ordered transactions against
the same two-slot storage contract. Original host-aware Core runs through
`ContractRuntime`, retaining the committed world and using a fresh local heap
for each call. The Rust path mines transactions and reads their actual output
and committed storage; imported Hull supplies the third execution history.
Initial storage and every completed prefix must agree. Six external scenarios
covering fifteen transactions, followed by exact archive replay, pass on all
three paths. Native generation, checked reduction candidates and strict case
replay are available through `semantic-storage-tool`; the separate
[storage runner](scripts/semantic-storage-differential.py) performs fresh
three-way comparisons. Bounded storage campaigns include failure-preserving
sequence reduction; all ten fixed scenarios and 27 transaction prefixes agree.

A separately versioned rollback profile writes both slots before reverting odd
inputs with a 32-byte payload; even inputs return normally. All eight external
scenarios and 21 transactions agree across the three paths, including retained
committed storage after each revert and exact archive replay. The fixed rollback
corpus passes native validation and actual three-way comparison for twelve
scenarios and 33 transaction prefixes. Failure reduction preserves reverted
outcomes and payload differences, including when earlier transactions are removed.

The bounded-call profile installs a funded parent and one child contract. It
compares both accounts' storage and balances, the root outcome, and ordered
committed logs after every transaction. Cases include child rollback, root
rollback, value transfers and aggregate steps with private mutable cells. All
ten external scenarios and 26 transactions agree across the three paths, and
exact archive replay passes. See the [call runner](scripts/semantic-call-differential.py)
and [usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-bounded-parentchild-calls).
All fourteen fixed call scenarios and 38 transaction prefixes match, and log
differences survive failure-preserving reduction and replay. M5 is complete for
these restricted profiles. Gas and nonce equivalence, arbitrary storage/accounts,
precompiles and deeper calls are outside these comparisons.

The generic profile instantiates one source selection function at Word, pair
and sum types, with a checked monomorphic Core reference. All 28 fixed cases
agree across the three paths. Saved-run replay and failure-preserving reduction
also pass, including type-preserving reduction of a runtime-input case.
See [generic comparisons](scripts/SEMANTIC_DIFFERENTIAL.md#compare-generic-selection).

The closure profile captures runtime Word values before outer-local assignments,
then reuses a closure or calls two independently captured closures. All 24 fixed
cases agree across Core, imported Hull and EVM; reduction preserves the capture
recipe, and saved-run replay passes. See
[captured closure comparisons](scripts/SEMANTIC_DIFFERENTIAL.md#compare-captured-closures).
The comptime profile compares Rust's compile-time evaluation with independent
Core execution of the original closed expression. All 32 fixed cases agree,
including all fifteen enabled constant-expression features. Reduction and
archive replay pass. See
[comptime comparisons](scripts/SEMANTIC_DIFFERENTIAL.md#compare-comptime-expressions).
The module profile combines these features across four source files with
explicit imports and exports. All 32 fixed cases agree across the three paths;
reduction and archive replay also pass, including replay after moving the
archive. See [module comparisons](scripts/SEMANTIC_DIFFERENTIAL.md#compare-module-bundles-and-mixed-features).
M6 is complete within these bounded profiles. This does not establish
language-wide coverage or prove source-emitter meaning preservation.

## Code layout

| Module | Contents |
| --- | --- |
| [Syntax](Solcore/Syntax.lean) | AST, lexer, parser, and parser proofs. |
| [TypeSystem](Solcore/TypeSystem.lean) | Types, substitutions, unification, and inference. |
| [Frontend.Current](Solcore/Frontend/Current.lean) | Source checking, staging, specialization, and compilation to Core. |
| [Frontend/RustHull](Solcore/Frontend/RustHull/) | Checked Rust Hull import, contract effects and Core execution. |
| [Core](Solcore/Core.lean) | Typed syntax, mutable cells, evaluator, execution machines, and safety proofs. |
| [SourceSemantics](Solcore/SourceSemantics.lean) | Independent source semantics and type preservation proofs. |
| [ContractRuntime](Solcore/ContractRuntime.lean) | Accounts, world state, host effects, calls, and transactions. |
| [Abi](Solcore/Abi.lean) / [Core.Wire](Solcore/Core/Wire.lean) | ABI encoding and the JSON representation of Core. |
| [Synthesis.Core](Solcore/Synthesis/Core.lean) | Checked program generation and shrinking for bounded execution profiles. |
| [Test](Solcore/Test/) | Tests and reusable fixtures, registered in [Tests/Main.lean](Tests/Main.lean). |

[Solcore.lean](Solcore.lean) provides the main import. The source-to-Core
correspondence proofs live under
[SourceSemantics/CoreLowering](Solcore/SourceSemantics/CoreLowering.lean).

## Contributing

Definitions and proofs live under `Solcore/`. Put tests under `Solcore/Test/`
and register them in `Tests/Main.lean`. Run the build, tests, and kernel check
above before submitting changes.

The [kernel check](scripts/check-kernel.mjs) rejects declarations such as
`sorry`, `axiom`, `partial`, and `unsafe` in semantic modules.
