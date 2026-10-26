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
mappings. See the [runtime API overview](docs/design/core-runtime-unification.md#public-runtime-api)
for values, handles, snapshots, and execution options.

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
expectations; generated differential comparisons use the separate runners below.

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
execution. Core typing does not establish the emitter's meaning preservation;
a separate [source emitter theorem](docs/design/scalar-emitter-meaning.md)
connects the closed, runtime-input, named-helper, raw-primitive, call-graph,
private-mutation, Word-aggregate, aggregate call-graph, call-graph loop,
aggregate loop and generic emitters' text to Core under an independent source
semantics and a stated Rust-pipeline boundary.

The [differential-testing milestones](docs/design/semantic-differential-testing.md)
specify source emission, seed replay, failure classification and reduction. A
single-case runner compares the original generated Core result, Rust-produced
EVM execution, and execution of Rust Hull on Lean Core. It saves all three
observations and verifies tools and artifact hashes during replay. A campaign
runner reduces failures while preserving their classification and disagreeing
paths, with explicit time, disk and attempt limits. Sonatina O0 is the default;
`--backend sonatina-o2` selects O2 for pure and stateful comparisons. Saved
archives and reductions retain that choice. Core fuel, EVM gas and process
timeouts remain separate resource limits.

Yul compiled by pinned solc is
available for the fourteen pure profiles with `--backend yul`. Its EVM bytes are
compared with original Core and with Hull using Sonatina O0 code images;
Yul object linking and stateful Yul are outside this comparison.
See [generated semantic comparisons](scripts/SEMANTIC_DIFFERENTIAL.md) for the
tools, supported operations and validation commands. Closed generated programs
may be constant-folded; source coverage is not runtime opcode coverage.

The [CI workflow](.github/workflows/semantic.yml) defines a complete fixed-corpus
gate for pull requests and recorded random seeds for daily and manual runs.
The same twenty-four-profile suite runs locally with shared time and disk limits.
It retains replayable findings and checks mismatch reduction and resource
classification using actual executions. See [suite preparation and operation](scripts/SEMANTIC_CI.md).

The `runtime-primitives` profile adds division/remainder, shifts, signed
operations, byte selection, sign extension, exponentiation, leading-zero count
and modular arithmetic through raw opcode wrappers. Its 81-case corpus covers
zero divisors/moduli, signed and 256-bit boundaries, and argument ordering.
Generated cases, typed reduction and strict replay use a separate version so
older profiles retain their saved-case semantics.
The eleven profiles whose step functions use the aggregate renderer
(aggregates, loops, generics, closures, comptime and module steps, and the five
stateful profiles) render the same raw primitives since emitter version 2,
importing the aliases only when a step uses one. Programs without a primitive
keep byte-identical source; older saved cases of these profiles are rejected by
their version check. See [raw primitives in aggregate-based step functions](scripts/SEMANTIC_DIFFERENTIAL.md#raw-primitives-in-aggregate-based-step-functions).

The `runtime-call-graphs` profile generates expressions directly with the
runtime input in scope. One to three helpers may call any earlier helper inside
operands, local bindings and branches. Its 56-case corpus checks shared callees,
nested arguments and nine syntactic call structures, alongside typed reduction
and strict replay. These structural checks do not measure executed call paths.
The `runtime-call-graph-loops` profile uses such a graph as the step of an
actual bounded source `while` loop, compared with the existing finite Core loop
reference. Its 66-case corpus covers masks and iteration counts of zero, one,
three and seven alongside the same nine call structures.
The `runtime-aggregate-call-graphs` profile generates internal Word pairs, Word
sums, projections and case payload scopes composed with those helper calls.
Its 56-case corpus covers nine syntactic composition structures, such as calls
inside pair components and calls on case payloads, with binder-preserving
reduction. These inventories do not measure executed calls or payloads.

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

The keyed-storage profile extends the two-slot protocol to a two-Word ABI input
whose key selects an arbitrary slot. Each call writes the key slot, its wrapping
successor and a counter slot, so keys can alias the counter and one another;
odd inputs revert. Every case declares the slots it observes, and the Hull and
EVM paths must also show no nonzero committed slot outside them. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-keyed-storage-transactions).
All twelve fixed scenarios and 33 transaction prefixes match on Sonatina O0 and
O2, as do the sixteen recorded random scenarios. A slot difference survives
failure-preserving reduction to one transaction and exact archive replay.

The dynamic-array profile adds a bounded dynamic ABI value: `run(uint256 flags,
uint256[] values)` with zero to three elements in the canonical ABI encoding.
The source reads a lazily decoded calldata array; original Core follows the
same head offset and length. Each element is folded through the checked step
into its own slot, and odd flags revert. Its twelve fixed scenarios and sixteen
recorded random scenarios match on both Sonatina levels, with reduction of
transactions and array elements and exact archive replay. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-bounded-dynamic-arrays).

The event-log profile makes committed logs observations. Up to three static
sites, each guarded by a flags bit, emit LOG0 to LOG4 through the pinned
`std.opcodes` wrappers with topics and data derived from the checked step;
odd flags revert after every log. Each transaction's ordered logs (emitter,
topics and data) are compared on all three paths, reverted transactions must
commit none, and the EVM chain's complete log list must equal the committed
receipts' logs. Core's host offers only a one-topic word log, so the Core
contract writes each site as a versioned frame of word logs that the observer
decodes. Its twelve fixed scenarios match on both Sonatina levels, as do the
sixteen recorded random scenarios on O0. On O2 fifteen match and one crashes
the compiler, a retained finding. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-committed-event-logs).

The call-value profile sends value with each transaction and makes the
contract's own committed balance an observation. The payable `run(uint256
flags, uint256 input)` reads the value through the pinned `std.opcodes`
`callvalue` wrapper, folds it into the checked step's input and accumulates
accepted value in a second slot; odd flags revert, which must refund the value.
Original Core runs each call in its balanced top-level execution, which
transfers the value before the call. The contract is deployed with a recorded
value of 0 or 5, and every committed balance must equal that value plus the
accepted total; the sender's balance is not observed. Its twelve fixed
scenarios and sixteen recorded random scenarios match on both Sonatina levels,
with reduction of transactions, values and the deployment value and exact
archive replay. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-nonzero-call-value).

The bytes profile adds one bounded dynamic `bytes` value: `run(uint256 flags,
bytes payload)` with 0 to 64 bytes in the canonical head/tail encoding with
zero padding. The pinned dialect decodes `bytes` only into memory; original
Core reads the calldata directly. The contract folds each present 32-byte
chunk through the checked step, recording each result in its own slot, and
records the payload length and last byte; odd flags revert. Its twelve fixed
scenarios and sixteen recorded random scenarios match on both Sonatina levels,
with reduction of transactions, payloads and the step and exact archive
replay. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-bounded-dynamic-bytes).

The forwarded-value profile has one contract send value to another. The sender
pays the parent a call value, and the parent forwards a bank amount to the
child through the pinned raw `call` wrapper; original Core uses its
value-carrying contract call. Each contract folds the value it receives into
its own slots, and the input selects whether the child, the parent, both or
neither revert. Both contracts' committed balances are observed: a child
revert must leave the amount with the parent, a root revert must keep both
accounts, and the balances must account for every committed call value. Its
twelve fixed scenarios match on both Sonatina levels, as do the sixteen
recorded random scenarios on O0. On O2 fourteen match and two crash the
compiler, retained findings. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-value-forwarded-by-contracts).

The mapping profile stores through a `mapping(word => word)` field whose
entries live at Keccak-256 slots. The pinned std hashes the base slot before
the key, the reverse of Solidity's order, and the profile follows the dialect.
Original Core computes each slot with the Hull path's Keccak permutation and
digest code, which is proved against the independent Keccak specification;
the observer derives the declared slots with a separate Keccak implementation.
Each call updates an entry, its successor and a counter; odd flags revert. Its
twelve fixed scenarios and sixteen recorded random scenarios match on both
Sonatina levels, with reduction and exact archive replay. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-keccak-addressed-storage-mappings).

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
The [next implementation roadmap](docs/design/next-implementation-roadmap.md)
prioritizes CI and scheduled bounded campaigns, generated O2/Yul comparisons,
and additional runtime operations. The local runners exist; continuous CI
campaigns have not yet been deployed.

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
