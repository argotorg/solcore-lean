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
expectations. [semantic-fixtures.py](scripts/semantic-fixtures.py) also runs
the recorded steps, and seeded single-change mutants of their inputs, on
checked Hull in Lean Core, Sonatina O0 and O2, and Yul, and compares the paths
with each other. No original Core exists for these fixtures, so this compares
compiled paths only: all 1,382 recorded steps agree on every admitted path,
none of 4,308 mutants disagrees, and Sonatina O2 crashes on one fixture, a
recorded finding ([pinned fixtures across paths](scripts/SEMANTIC_DIFFERENTIAL.md#compare-the-pinned-end-to-end-fixtures-across-paths)).
Calls whose arguments are user data types under std's derived ABI also get
every boundary Word of their tags, dynamic offsets and `bytes` lengths: all
519 such mutants of the 26 recorded calls agree on every path. Sequence mutants
carry one change forward instead of rolling it back: a committed mutant or
method directive, or a dropped, duplicated or swapped step, with every later
step compared across the paths. In a run of the 117 fixtures with two or more
recorded calls, all 5,462 steps compared after the change in 558 such mutants
agree on every path.
Generated differential comparisons use the separate runners below.

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
Random campaigns of the seventeen G0-based profiles use the generator's fourth
revision: the second revision, which mixes each draw and widens its bank of
boundary literals, under a per-case swarm mask that enables about half of the
operators and forms, restricted to those the profile's emitter renders. Random
stateful steps use the third revision, which keeps the whole mask, and fixed
corpora keep the first
([G0 generator revisions](scripts/SEMANTIC_DIFFERENTIAL.md#g0-generator-revisions)).
Emitter regressions include actual checked Rust compilation and imported-Hull
execution. Core typing does not establish the emitter's meaning preservation;
a separate [source emitter theorem](docs/design/scalar-emitter-meaning.md)
connects the closed, runtime-input, named-helper, raw-primitive, call-graph,
private-mutation, Word-aggregate, aggregate call-graph, call-graph loop,
aggregate loop, generic, two-slot storage, storage rollback, keyed storage and
event-log emitters' text to Core under an independent source semantics and a
stated Rust-pipeline boundary.

The [differential-testing milestones](docs/design/semantic-differential-testing.md)
specify source emission, seed replay, failure classification and reduction. A
single-case runner compares the original generated Core result, Rust-produced
EVM execution, and execution of Rust Hull on Lean Core. It saves all three
observations and verifies tools and artifact hashes during replay. A campaign
runner reduces failures while preserving their classification and disagreeing
paths, with explicit time, disk and attempt limits; a pure campaign compiles
each distinct source once per backend and shares it among its cases. Sonatina O0
is the default; `--backend sonatina-o2` selects O2 for pure and stateful
comparisons. Saved archives and reductions retain that choice. Core fuel, EVM
gas and process timeouts remain separate resource limits.

Yul compiled by pinned solc is
available for the twenty-seven pure profiles with `--backend yul`, and for the
twenty-seven storage-family profiles and the call-return and call-sequence
profiles when they are selected. Its EVM bytes are
compared with original Core and with Hull using Sonatina O0 code images. Yul
object linking and the other two call profiles, which compile a parent and a
child contract from one source, are outside this comparison.
See [generated semantic comparisons](scripts/SEMANTIC_DIFFERENTIAL.md) for the
tools, supported operations and validation commands. Closed generated programs
may be constant-folded; source coverage is not runtime opcode coverage.

The [CI workflow](.github/workflows/semantic.yml) runs the complete fixed-corpus
gate and recorded random seeds. Its automatic triggers are disabled for now, so
it runs only on manual dispatch.
The same fifty-eight-profile suite runs locally with shared time and disk limits.
It retains replayable findings and checks mismatch reduction and resource
classification using actual executions. See [suite preparation and operation](scripts/SEMANTIC_CI.md).
[Continuous fuzzing](scripts/SEMANTIC_CI.md#continuous-fuzzing) repeats random
suites with advancing seeds and counts their findings in a signature registry.
Upstream findings already recorded whose signatures are stable symptoms, such
as known compiler crashes and rejections, count as known rather than new. So do
the mismatches of a recorded semantic defect that fall in its mismatch class,
such as Sonatina O0's other Words for loops that write std memory values.
An opt-in run kind also runs the pinned fixture comparison in mutation mode,
a slice of the fixtures per iteration within per-fixture and per-run budgets.

The `runtime-primitives` profile adds division/remainder, shifts, signed
operations, byte selection, sign extension, exponentiation, leading-zero count
and modular arithmetic through raw opcode wrappers. Its 81-case corpus covers
zero divisors/moduli, signed and 256-bit boundaries, and argument ordering.
Generated cases, typed reduction and strict replay use a separate version so
older profiles retain their saved-case semantics.
The eleven profiles whose step functions used the aggregate renderer at
emitter version 2 (aggregates, loops, generics, closures, comptime and module
steps, and the five stateful profiles of that time) render the same raw
primitives since that version, as do the profiles added on that renderer
later, such as nested loops and recursion; the aliases are imported only when
a step uses one. Programs without a primitive keep byte-identical source; older
saved cases of these profiles are rejected by their version check. See [raw primitives in aggregate-based step functions](scripts/SEMANTIC_DIFFERENTIAL.md#raw-primitives-in-aggregate-based-step-functions).

The `runtime-assembly` profile renders the same primitive functions as inline
Yul: the whole body in one `assembly` block, with each conditional as a Yul
`switch` or as two Yul `if`s, or each operation in its own block assigning a
Solcore local. Its original Core is the primitive function itself, so only the
source differs. The 72-case corpus combines the primitive corpus's functions
in each of the three forms at the eight boundary inputs
([inline Yul](scripts/SEMANTIC_DIFFERENTIAL.md#compare-inline-yul)).
The `runtime-assembly-loops` profile renders a call-graph loop plan as one
`assembly` block: the helpers become Yul functions and the loop a Yul `for`
loop, in five forms that use a plain loop, `break`, `continue`, `leave` from a
Yul function, and helpers with two return values. Its original Core is the
call-graph loop plan itself. All 90 fixed cases match on O0, O2 and Yul. In
random runs of eight functions, 70 of 80 cases match on each backend and one
function's ten cases crash the compiler, a retained finding
([inline Yul loops and functions](scripts/SEMANTIC_DIFFERENTIAL.md#compare-inline-yul-loops-and-functions)).
The `runtime-assembly-memory` profile passes a primitive function's argument
and results through memory in one `assembly` block: Word and byte writes, and
Word reads at the same, overlapping and unaligned offsets, in a 96-byte window
above the unmoved free-memory pointer, optionally followed by `keccak256` over
0 to 64 written bytes. Its original Core keeps no memory: the window is three
Words updated with shifts and masks, and the hash a closure built from Core's
Keccak permutation. All 80 fixed cases match on O0, O2 and Yul. In random runs
of eight functions, all 96 cases match on O0 and Yul, and on O2 one function's
twelve cases crash the compiler, a retained finding
([inline Yul memory](scripts/SEMANTIC_DIFFERENTIAL.md#compare-inline-yul-memory)).
The `runtime-enums` profile declares one to three plain or generic
user-defined enums of two to four constructors, builds their values from the
input and matches them with nested constructor and tuple patterns, wildcards
and nested matches. Its original Core never reads the source: an enum is the
right-nested sum of its payloads and a `match` nested `caseE` with
fall-through thunks, admitted only when every arm is useful and the match is
exhaustive. All 56 fixed cases and 96 random cases of eight functions match on
O0, O2 and Yul
([user-defined enums and match](scripts/SEMANTIC_DIFFERENTIAL.md#compare-user-defined-enums-and-match)).
The `runtime-traits` profile calls one trait with a unary and a binary method
at instances built from Words, tuples, std sums and user-defined enums,
directly and through constrained generic functions. The binary method of the sum impl
matches its second argument inside each arm, a shape with a past upstream
defect. Its original Core has one closure per reached instance and method,
built bottom-up. All 40 fixed cases and 96 random cases of eight functions
match on O0 and O2. On Yul, 32 and 84 of them match, and solc rejects one
plan's specialized binary method in each run with `StackTooDeepError`, a
recorded finding
([traits and constrained generic impls](scripts/SEMANTIC_DIFFERENTIAL.md#compare-traits-and-constrained-generic-impls)).
The `runtime-trait-hierarchies` profile adds a subclass of that trait, as a
marker or with its own method-level generic, and a chain of two such bounds.
It calls them directly, through subclass-bounded helpers, through method values
and through generic function values. All 104 fixed cases match on O0 and O2,
and 96 match on Yul, where solc rejects one plan's base-trait method with
`StackTooDeepError` as for traits. Random plans keep a base method reached
through two superclass bounds at tuples, sums and generic enums, which the
checked frontend rejects on every backend, a recorded finding; the other 72
of 96 random cases match on all three backends
([trait hierarchies and method-level generics](scripts/SEMANTIC_DIFFERENTIAL.md#compare-trait-hierarchies-and-method-level-generics)).
The `runtime-memory-values` profile builds std's memory values in pure code:
`memory<bytes>` values from Words, concatenations and slices, `memory_ref`
views, second variables and Word arrays, written inline or through helpers and
read through std's range checks, `keccak256_` and array access, in straight-line
code and bounded loops. Its original Core models the values as byte lists with
slices as views and computes the returned Word itself; an out-of-range access
is std's `OutOfBounds()` revert, compared exactly. All 232 fixed cases and 96
random cases of eight functions match on O2 and Yul. Sonatina O0 returns other
Words for 4 fixed and 8 random cases whose loops use memory values, a recorded
finding ([Solcore memory values](scripts/SEMANTIC_DIFFERENTIAL.md#compare-solcore-memory-values)).
The `runtime-memory-calls` profile passes those values across calls in
straight-line code: one to three helpers read them, write through them and
return them, a slice of them or a fresh copy, pack them into a pair or take
them out of a pair, std sum or user enum, and call earlier helpers; generic
helpers over std's memory traits run at more than one type, and function
values and closures carry them. Its original Core inlines every call into the
same byte-list model, so a returned argument is the caller's value and a
written argument is seen by the caller. All 328 fixed cases and 96 random
cases of eight functions match on O0, O2 and Yul
([Solcore memory calls](scripts/SEMANTIC_DIFFERENTIAL.md#compare-solcore-memory-calls)).
The `runtime-revert-data` profile reverts with std's `Error` values made from
the input: `Error(w)`, whose revert data are the low four bytes of a run-time
selector Word, `Error.Empty`, and `Error.Msg` over a `memory<string>` view of a
bytes value, raised by `revertWithError` or `require`, beside `require` with a
literal message, `revertLit` and `revertEmpty()`. Sites run in helpers, two
helpers deep, function values, closures, pair, sum and enum arms and a bounded
loop, and a message's bytes written after its `Error` was made, also through a
second variable, are seen. Original Core carries revert data of up to 64 bytes
in the same byte-list model, and the paths compare them exactly. All 152 fixed
cases and 96 random cases of eight functions match on O0, O2 and Yul
([Solcore revert data](scripts/SEMANTIC_DIFFERENTIAL.md#compare-solcore-revert-data)).

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
for each function's inputs. Random campaigns of the runtime-input profiles also
run each function at four inputs derived from the case seed after its boundary
inputs, and in the eighteen profiles whose functions can be identities they
exclude a function that returns every boundary input unchanged
([boundary identities](scripts/SEMANTIC_DIFFERENTIAL.md#boundary-identities)).
A further profile supports one to three acyclic
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
Nested bounded loops run a second bounded `while` inside the first, with up to
nine step calls, against an unrolled finite Core reference; all 72 fixed
nested-loop cases match on O0, O2 and Yul
([nested bounded loops](scripts/SEMANTIC_DIFFERENTIAL.md#compare-nested-bounded-loops)).
Bounded recursion calls a recursive source function, or two that call each
other, to a depth of up to seven taken from the input, against an unrolled
finite Core reference; all 63 fixed recursion cases match on O0, O2 and Yul
([bounded recursion](scripts/SEMANTIC_DIFFERENTIAL.md#compare-bounded-recursion)).
Two profiles compose these constructs: a loop body that creates a closure
capturing a loop-carried local and applies it in the same iteration, and a
bounded loop inside every frame of the three recursion forms, each against
unrolled finite Core references. All 48 fixed loop-closure and 78 fixed
recursive-loop cases match on O0, O2 and Yul
([composed control flow](scripts/SEMANTIC_DIFFERENTIAL.md#compare-composed-control-flow)).
M1 through M4 are complete for these restricted profiles.

The first stateful profile compares one to three ordered transactions against
the same two-slot storage contract; random campaigns of every stateful profile
extend sequences to eight transactions. Original host-aware Core runs through
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
these restricted profiles. Gas and nonce equivalence, accounts other than the
installed contracts, precompiles and deeper calls are outside these comparisons.

The keyed-storage profile extends the two-slot protocol to a two-Word ABI input
whose key selects an arbitrary slot. Each call writes the key slot, its wrapping
successor and a counter slot, so keys can alias the counter and one another;
odd inputs revert. Every case declares the slots it observes, and the Hull and
EVM paths must also show no nonzero committed slot outside them; the
whole-storage comparison below extends this to original Core. See the
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

The ledger profile keys the mapping profile's entries by each transaction's
sender. Three funded senders call one contract, which credits the sender's
entry with the step's result and moves an amount to a recipient's entry; an
insufficient balance reverts without writing, and odd flags revert after the
writes. Original Core reads each invocation's caller, a separate Hull runner
accepts the declared senders, and the EVM path sends each transaction from its
sender. Besides agreeing, every completed row must follow the ledger's rules
from the prior committed slots. Its twelve fixed scenarios and sixteen
recorded random scenarios match on both Sonatina levels, with reduction and
exact archive replay. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-a-sender-keyed-mapping-ledger).

The long-bytes profile extends the bytes profile to payloads of up to 256
bytes, folding up to eight 32-byte chunks through the checked step into their
own slots, which generalizes the bytes profile's two-chunk contract. Its
twelve fixed scenarios and sixteen recorded random scenarios match on both
Sonatina levels, with reduction and exact archive replay. Static multi-word,
bounded `bytes` and enum return values came later, with their own contract
entry conventions (below). See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-bytes-payloads-beyond-64-bytes).

The nested-array profile passes one bounded `uint256[][]` parameter, at most
three rows of at most two elements, in the canonical nested head/tail
encoding. The pinned std follows each row's offset relative to the offset
table; original Core reads the calldata directly. The contract folds each
present element through the checked step into its own slot, then records the
outer length and the element count; odd flags revert. Its twelve fixed
scenarios and sixteen recorded random scenarios match on both Sonatina levels,
with reduction and exact archive replay. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-nested-dynamic-arrays).

The malformed-calldata profile sends the dynamic-array contract calldata with
one malformation per transaction, at most 1 KiB and without value: short
calldata, a wrong selector, truncation, trailing bytes, out-of-range, wrapping
or overlapping head offsets, and over-long, wrapping or short lengths. Its
original Core contract evaluates the pinned std's dispatcher and decoder checks
on the actual calldata in std's order, then runs the dynamic-array protocol on
the decoded words. A std rejection reverts with a four-byte error selector,
while original Core's contract entry returns one Word, so such a row is compared
by selector. The rule applies only when original Core reverts with exactly that
selector as a Word and the transaction's std prescription is that rejection;
Rust EVM and imported Hull must then revert with exactly those four bytes. Every
other row, and Hull against EVM in every row, is compared exactly, and each
analysis lists the rows compared by selector. Golden cases fix std's outcome for
each malformation. Its thirteen fixed scenarios and sixteen random scenarios at
each of two node budgets match on both Sonatina levels. See the
[usage guide](scripts/SEMANTIC_DIFFERENTIAL.md#compare-malformed-calldata).

Two more profiles send malformed calldata to other contracts under the same
selector rule. The malformed nested-array profile adds out-of-range, wrapping
or overlapping row offsets and over-long or wrapping row lengths. Std checks
the outer array and its offset table when it decodes the parameter, but a row
only when the body reads it, after the earlier rows are folded and written;
original Core's contract makes the same checks at the same points. The
malformed-bytes profile sends the 256-byte `bytes` contract out-of-range or
wrapping offsets, lengths past the data, cuts inside the payload, cuts inside
its padding, which std never reads, and nonzero padding, which std ignores.
Golden cases, 64 for nested arrays and 40 for `bytes`, fix std's outcome for
each malformation and its decode order. Each profile's thirteen fixed scenarios
and sixteen random scenarios at each of two node budgets match on both Sonatina
levels. See
[malformed nested arrays](scripts/SEMANTIC_DIFFERENTIAL.md#compare-malformed-nested-arrays)
and [malformed bytes](scripts/SEMANTIC_DIFFERENTIAL.md#compare-malformed-bytes).

The several-methods profile gives one contract two to four external methods
over shared slots, each with its own checked step. Method names, and so the
selectors and their order, are drawn per scenario. Original Core dispatches as
the pinned std does: it compares the selector Word with each method's selector
in declaration order, reverts with std's fallback selector on short calldata or
a missing selector, and checks the called method's argument head before it
runs. Transactions call recorded methods or send a recorded missing selector,
which is compared under the same selector rule. Golden cases fix std's
dispatch for 110 single calls. The twelve fixed scenarios and sixteen random
scenarios at each of two node budgets match on both Sonatina levels. See
[several methods](scripts/SEMANTIC_DIFFERENTIAL.md#compare-several-methods).

The storage-loop profile runs a bounded source `while` loop over declared
slots. Each iteration reads slot 0, slot 1, the slot the previous iteration
wrote and its own slot, which an earlier transaction may have written, and
writes its step result to its own slot and to slot 0. The iteration count is
the input under a mask of at most seven, and original Core unrolls the loop
into finite guards over literal slots. The twelve fixed scenarios and sixteen
random scenarios at each of two node budgets match on both Sonatina levels and
on Yul. See
[storage-writing loops](scripts/SEMANTIC_DIFFERENTIAL.md#compare-storage-writing-loops).

The Keccak-loop profile runs the same kind of bounded loop over std mapping
entries. Each iteration hashes its entry's slot from the counter and the
input, reads and writes the entry and slot 0, and emits one log with the
counter and the key as topics and the written value as data, so Keccak,
memory, storage and log lowering meet inside a loop body. A key mask decides
which iterations share an entry, and transactions whose inputs share their
high bits share entries too. The thirteen fixed scenarios and sixteen random
scenarios at each of two node budgets match on both Sonatina levels and on
Yul, with every log compared. See
[loops over Keccak-addressed entries](scripts/SEMANTIC_DIFFERENTIAL.md#compare-loops-over-keccak-addressed-entries-and-logs).

Two more profiles render the storage-loop and Keccak-loop plans with every
storage read and write, entry hash, log and completion in inline Yul
`assembly` blocks around the Solcore step call. Three forms recompute the slot
in each block, carry it in a Solcore local, or pipeline each iteration's
writes with the next iteration's reads. A Yul block can call only builtins and
its own Yul functions, so the loop stays a Solcore `while` loop. Original Core
is the parent plans' unchanged reference. The sixteen and nineteen fixed
scenarios and sixteen random scenarios of each at two node budgets match on
both Sonatina levels and on Yul. See
[storage and Keccak loops through inline Yul](scripts/SEMANTIC_DIFFERENTIAL.md#compare-storage-and-keccak-loops-through-inline-yul).

The tuple-return profile's method returns a static ABI tuple of two to four
Words, and all three paths compare the whole return data. Original Core
returns it through a new contract entry convention, `wordTupleOutcomeV1`,
which decodes right-nested Word pairs into their concatenated Words; reverts
and traps still carry one Word. A nested word call carries one Word, so the
one-level nested executor treats a tuple contract as unavailable to calls and
creation, and the one-Word theorems take that as a premise. The twelve fixed
scenarios and sixteen random scenarios at each of two node budgets match on
both Sonatina levels and on Yul. Original Core has no variable-length value,
so `bytes` returns take a bounded convention of their own (below). See
[ABI-encoded tuple returns](scripts/SEMANTIC_DIFFERENTIAL.md#compare-abi-encoded-tuple-returns).

The bytes-return profile's method returns a `memory<bytes>` value of zero to
64 bytes, built from the step result and the committed slots, and all three
paths compare the whole return data, std's zero padding included. Original
Core returns it through a second entry convention, `boundedBytesOutcomeV1`:
the empty value, or a length tag with two data Words, which decode to std's
canonical encoding of the offset, the length and the data padded to whole
Words. Like a tuple contract, it is unavailable to nested word calls and
creation. The twelve fixed scenarios and sixteen random scenarios at each of
two node budgets match on both Sonatina levels and on Yul. See
[bounded `bytes` returns](scripts/SEMANTIC_DIFFERENTIAL.md#compare-bounded-bytes-returns).

The enum-return profile's method returns a value of a user-defined enum of two
to four constructors, each with no fields, one or two Words or one `bytes`
value of at most 64 bytes, and all three paths compare the whole return data.
Original Core returns it through a third entry convention, `enumOutcomeV1`: a
right-nested sum of constructor values, each pairing its tag Word with its
fields, where Lean's Keccak-256 computes the tags from the constructors'
signatures. They decode to std's `ABIGeneric` encoding: inline for a static
enum, behind an offset for one with a `bytes` constructor, and zero-padded to
the widest constructor. Like the other two conventions, it is unavailable to
nested word calls and creation. The fifteen fixed scenarios and sixteen random
scenarios at each of two node budgets match on both Sonatina levels and on
Yul. See
[returned enums](scripts/SEMANTIC_DIFFERENTIAL.md#compare-returned-enums).

The enum and struct storage profile keeps user-defined enum and struct values
in contract fields and behind two keys of two mappings through
`std.StorageGeneric`. Up to twelve methods write, clear and read them and
update one field of a record. Its original Core lays out the enum's nested
tags and payloads over the declared slots and the mapping's Keccak closure
itself, so a shorter variant written over a longer one, stale payload slots,
field offsets and neighbouring keys are all observed. The 26 fixed scenarios
and sixteen random scenarios at each of two node budgets match on both
Sonatina levels and on Yul. Imported Hull deploys its larger contracts from O0
images with up to 15,000,000 fuel, so the suite's Hull fuel bound is now
40,000,000. See
[enum and struct values in storage](scripts/SEMANTIC_DIFFERENTIAL.md#compare-enum-and-struct-values-in-storage).

The enum-argument profile's method takes a value of a user-defined enum of two
to four constructors, each with no fields, one or two Words, a struct of two
Words or one `bytes` value, which std's derived decoder reads: inline for a
static enum, behind an offset for one with a `bytes` constructor.
Transactions mix canonical encodings with twelve malformations, among them
unknown tags, truncation, bad offsets and overlong `bytes` lengths. Original
Core decodes the calldata itself in std's order, with the selector and tags
from Lean's Keccak-256. The paths compare std's error selectors and an unknown
tag's empty revert data by rule. The 21 fixed scenarios and sixteen random
scenarios at each of two node budgets match on both Sonatina levels and on
Yul. See [enum arguments](scripts/SEMANTIC_DIFFERENTIAL.md#compare-enum-arguments).

The enum-array profile's method takes a calldata array of up to three values
of such an enum and two indices. std checks the array's head at dispatch and
reads the two indexed elements through `abiArrayGet`, static elements inline
and dynamic ones behind an offset table. Transactions mix canonical encodings
with fourteen malformations, among them array lengths and offsets beyond the
calldata, element offsets into the offset table, shared bodies, retags and
out-of-range indices. Original Core decodes the head and both elements itself
in std's order. The paths compare std's error selectors, `ArrayOutOfBounds()`
among them, and an unknown tag's empty revert data by rule. The 17 fixed
scenarios and sixteen random scenarios at each of two node budgets match on
both Sonatina levels and on Yul. See
[enum arrays](scripts/SEMANTIC_DIFFERENTIAL.md#compare-enum-arrays).

The array-return profile's method returns std's ABI encoding of a memory array
of zero to three `uint256`, `bytes4`, `bytes` or `uint256[]` elements, and all
three paths compare the whole return data: the offset and the count, inline
Words or an offset table, and each `bytes` or inner array's tail, with std's
zero padding over dirty memory past each `bytes` length. The pinned compiler
refuses a declared array output, so the method declares a Word return and ends
as std's dispatcher does, with `abi_encode` and the `return_` opcode. The
element type is fixed per contract, while the count and the inner lengths are
read at run time from the arguments, so no optimizer folds std's encoder
loops. Original Core builds every Word itself and returns them through
`wordTupleOutcomeV1`. The 23 fixed scenarios and sixteen random scenarios at
each of two node budgets match on both Sonatina levels and on Yul. See
[returned arrays](scripts/SEMANTIC_DIFFERENTIAL.md#compare-returned-arrays).

The constructor-argument profile deploys a contract whose constructor takes
none, one or two Words, a Word and a `bytes` value of up to 64 bytes, or a Word
and a user-defined enum. The init code carries the arguments' ABI encoding,
canonical or with one malformation such as truncation, an offset or length
beyond the end, an unknown or cut tag, trailing bytes or a static enum cut to a
narrower head. The compiler's derived deployment code decodes them with std's
memory reader, with no up-front head check. Original Core runs an initializer
over the argument bytes as the deployment phase and installs the runtime with
its storage on return, nothing on a revert. All three paths compare the
deployment row, its status, revert data and whole storage, before the runtime
transactions, and a failed deployment ends the scenario. The 40 fixed scenarios
and sixteen random scenarios at each of two node budgets match on both Sonatina
levels and on Yul. See
[constructor arguments](scripts/SEMANTIC_DIFFERENTIAL.md#compare-constructor-arguments).

The call-return profile compiles a parent and a child contract each from its
own source. The parent calls a child method through std's `raw_call` and
decodes the returned tuple of two to four Words, `bytes` value of up to 64
bytes or user-defined enum with std's memory reader. The child returns the
value through std's encoder, or raw through `return_` with one malformation
such as truncation, trailing bytes, an offset, length or tail beyond the end,
an unknown or cut tag or a static enum cut to a narrower head. Original Core
cannot read return data, so an additive call-and-resume convention in the
contract runtime splits the parent at its one call: a call phase, the child,
then a resume phase that reads the child's status and bytes as its input, each
through the public top-level runner. Each transaction records std's
prescribed rejection from a byte-level Lean model, which the adapter
recomputes. The 45 fixed scenarios and sixteen random scenarios at each of two
node budgets match on both Sonatina levels and on Yul. See
[call returns](scripts/SEMANTIC_DIFFERENTIAL.md#compare-call-returns).

The call-sequence profile's parent calls the child two or three times in one
method and reads `returndatasize` and an in-bounds `returndatacopy` window in
inline Yul before and after each call, so a stale return-data buffer or a read
moved across a later call would show. The child returns or reverts raw data of
0 to 96 bytes. An additive call chain in the contract runtime splits original
Core's parent at every call; the one-call convention is the chain without
middle phases. The 16 fixed scenarios and sixteen random scenarios at each of
two node budgets match on both Sonatina levels and on Yul. See
[call sequences](scripts/SEMANTIC_DIFFERENTIAL.md#compare-call-sequences).

All thirty-one stateful profiles also compare the installed contracts' whole
committed storage after deployment and after every transaction. Original
Core's accounts keep an exact ordered list of their present slots, imported
Hull lists its committed entries, and the EVM path rereads every slot that
Anvil's `prestateTracer` diffs have reported since deployment;
`scripts/check-evm-storage-diff.py` checks that method on a hand-written probe.
Deployment must leave the storage empty, or exactly the decoded record for the
constructor-argument profile, and a revert must leave each path's whole storage
unchanged. The latest fixed run of all thirty-one profiles, 505 scenarios and
1,278 transaction prefixes, matched on Sonatina O0, and every
corpus has also matched on O2 with whole storage compared. A synthetic stray
write that the declared slots could not see is caught and reduced to one
transaction. See
[whole committed storage](scripts/SEMANTIC_DIFFERENTIAL.md#compare-whole-committed-storage).

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
