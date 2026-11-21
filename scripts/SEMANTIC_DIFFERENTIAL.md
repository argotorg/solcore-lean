# Generated semantic comparisons

This page explains the generated differential tests: what a comparison runs, how to run one,
what each profile generates and how its Core reference models it, and what is known to fail.
The comparison model and the rules for reading a disagreement are in the developer guide's
[differential-testing page](../docs/guide/differential-testing.md). Tool preparation, the
all-profile suites, CI and continuous fuzzing are in
[Running the semantic test suite](SEMANTIC_CI.md).

The reference Rust revision is `d1b5ac28c0a5821c1a56758f182e27bc5e7c4f09`, upstream main of
2026-11-16; before it the pin was `e2eef194`, and before that `2a745e12`.

Run records up to 2026-11-17 are in git history at `049f8ce1f`.

## How a comparison works

A case is a generated Core program with one runtime input (pure profiles), or a generated Core
contract with an ordered transaction sequence (stateful profiles), together with the Solcore
source emitted from it. A comparison runs the case on three paths:

1. **Original Core.** Lean evaluates the generated Core program itself. It is the primary
   reference.
2. **Rust EVM.** The pinned Rust compiler checks the emitted source. Its Sonatina O0 or O2 code
   images, or its Yul compiled by solc, run on a local Anvil.
3. **Imported Hull.** The checked Hull that Rust exported is imported into Lean and executed on
   Core with the linked Sonatina images.

A case passes only when all three paths complete and all three pairwise comparisons agree. No
saved expected result is trusted: replay recomputes every observation. Source rejection,
compiler crashes, execution errors, semantic mismatches, unsupported scope and resource limits
stay distinct outcomes, and only `matched` counts as agreement. Core fuel and EVM gas are
separate budgets, and insufficient gas never counts as a wrong return value.

| Backend | EVM path | Imported Hull images |
| --- | --- | --- |
| `sonatina-o0` (default) | Sonatina O0 | Sonatina O0 |
| `sonatina-o2` | Sonatina O2, the real O2 pipeline | Sonatina O2 |
| `yul` | solc `0.8.35+commit.47b9dedd` with optimization and Osaka | Sonatina O0 |

Both Sonatina levels use the pinned Sonatina revision and its linker symbol extents. On Yul the
EVM deploys solc's creation bytes and checks the installed runtime against the same
compilation's deployed bytes. Imported Hull keeps Sonatina O0 images, recorded in
`pathBackends`, so a Yul run compares observations that do not depend on code layout and makes
no claim of Yul-linked Hull execution. No backend silently falls back to another.

Profiles come in three families, each with its own runner and campaign:
- **pure:** one function of one runtime Word, called once per case (`semantic-differential.py`,
  `semantic-campaign.py`);
- **storage:** one contract and a transaction sequence, with committed state observed after
  every transaction (`semantic-storage-differential.py`, `semantic-storage-campaign.py`);
- **call:** a parent and a child contract (`semantic-call-differential.py`,
  `semantic-call-campaign.py`).

The storage and call families are the stateful profiles. Coverage on this page means source AST
or plan coverage of matched cases. It never claims that a backend executed a particular opcode:
Rust can fold closed G0 computations, and only a runtime-input profile supports an opcode claim.

**Proofs.** For the closed G0, runtime-input, named-helper, raw-primitive, call-graph,
private-mutation, aggregate, aggregate call-graph, call-graph loop, aggregate loop, generic,
two-slot storage, storage rollback, keyed storage and event-log emitters, a kernel-checked
theorem relates the emitted text to the original Core result under an independent source
semantics; for the storage and event-log emitters, to its top-level transaction. It assumes Rust
parsing, typing, compilation and execution; see
[scalar emitter meaning](../docs/design/scalar-emitter-meaning.md). The checker soundness theorem
gives the Core typing of admitted programs. Outside these theorems, agreement is test evidence,
not a preservation proof.

## Run comparisons

### Build and generate

`python3 scripts/prepare-semantic-tools.py --prepare` builds every native tool and the pinned
Rust exporters ([tools](SEMANTIC_CI.md#tools)). For the pure profiles alone, and a first corpus:

```sh
lake build semanticCaseTool rustHullContract rustHullScenario
mkdir -p .upstream/semantic-cases
.lake/build/bin/semantic-case-tool generate 0 24 12 2000 1000000 \
  > .upstream/semantic-cases/corpus.json
```

- The arguments are `SEED NODES COUNT ATTEMPTS FUEL`. Seeds are tried consecutively from `SEED`,
  and every attempt and exclusion is counted. Limits per call: 512 nodes, 1,024 cases, 10,000
  attempts and fuel 10,000,000; the seed is an exact unsigned 64-bit decimal integer.
- A corpus whose `status` is `generation-exhausted` has fewer cases than requested and is not a
  successful batch.
- A case holds the original Core Wire program, the emitted source, versioned provenance,
  contract metadata and a fresh direct Core observation.
- Every emitted file starts with `pragma solcore;`, which the pinned compiler requires first
  (`SC0002`), and the harnesses write each file exactly as emitted.
- An unsupported operation is an explicit exclusion, also in a branch that would not run; the
  generator never replaces it with another computation.
- `semantic-case-tool emit PROGRAM.json [FUEL]` checks an external Core Wire program against G0
  and renders it. `observe CASE.json [FUEL]` evaluates a case's original Core program without
  authenticating its source. `replay CASE.json [FUEL]` rechecks, regenerates and recomputes, and
  never trusts a saved `directCore`. `shrink CASE.json LIMIT [FUEL]` returns checked, smaller,
  re-emitted candidates, which the campaign must rerun to know whether they keep a mismatch.

The runners start their own loopback-only Anvil and need local listening sockets; they never use
an existing chain or a remote RPC endpoint. Yul runs also need solc, given with `--solc PATH`.

### Compare one case

```sh
python3 - <<'PY'
import json
from pathlib import Path
root = Path('.upstream/semantic-cases')
corpus = json.loads((root / 'corpus.json').read_text())
assert corpus['status'] == 'complete' and corpus['cases']
(root / 'case.json').write_text(json.dumps(corpus['cases'][0], indent=2) + '\n')
PY
python3 scripts/semantic-differential.py --case .upstream/semantic-cases/case.json \
  --output .upstream/semantic-cases/run
python3 scripts/semantic-differential.py --replay .upstream/semantic-cases/run \
  --output .upstream/semantic-cases/replay
```

- The output directory must be new. A run rechecks and re-emits the case, computes the original
  Core result, compiles checked Hull and exact images, deploys the bytes on Anvil and runs the
  same imported contract on Core. It exits zero only for `matched`.
- `--backend sonatina-o2` or `--backend yul --solc PATH` selects the backend. The pure, storage
  and call adapters, their campaigns and the suite take it. The storage adapter and campaign
  accept Yul for the twenty-seven storage-family profiles. The call adapter and campaign accept
  it for `stateful-call-returns`, `stateful-call-sequences` and `stateful-call-branches`, and
  reject it for `stateful-calls` and `stateful-forwarded-value`. Use one output directory per
  backend.
- Limits: `--direct-fuel`, `--core-fuel`, `--gas`, `--timeout`, `--total-timeout`,
  `--output-limit` and `--artifact-limit`, with defaults in `--help`.
- `report.json` records tool versions and hashes, compiler and exporter receipts, source and
  artifact hashes, inputs, budgets, process outcomes, raw observations and comparisons. A valid
  payload of the wrong ABI length is a semantic mismatch; malformed transport is an adapter
  error.
- Replay verifies every archive member, rejects missing or changed files and tool drift,
  restores the saved budgets and backend, and executes again. It rejects a conflicting
  `--backend`; a legacy report without a backend field means O0. Yul archives also keep the
  exact solc request and response, the Yul source and the compiler identity.
- An archive can be moved before replay. `--solc` may name the same executable at another path,
  but not another hash or version. To change budgets, backend or tools, rerun the saved
  `case.json` with `--case`: that is a new experiment, not an exact replay.

### Run a campaign

```sh
python3 scripts/semantic-campaign.py --corpus scripts/semantic-corpus.json \
  --output .upstream/semantic-ci --seconds 300 --disk-bytes 134217728
python3 scripts/semantic-campaign.py --seed 78 --nodes 32 --cases 16 --attempts 256 \
  --output .upstream/semantic-search --seconds 300 --disk-bytes 134217728 --shrink-attempts 32
```

- `--corpus` runs every entry of a fixed manifest with its recorded versions and inputs and
  checks its required coverage, counting only cases that match on all three paths.
- Otherwise the campaign searches from `--seed` with `--nodes`, `--cases` (individual inputs) or
  `--functions N` (whole functions) and `--attempts`. `--case` reruns a saved case. `--profile`
  is inferred from a saved case or corpus, otherwise it is `closed-g0`.
- Limits: `--seconds`, `--disk-bytes`, `--case-timeout`, `--direct-fuel`, `--core-fuel`, `--gas`,
  `--shrink-attempts` (all candidate executions) and `--shrink-candidates` (one batch). Time and
  disk are polled while children run; they are not OS quotas. SIGTERM or an interrupt stops
  owned children and writes the summary.
- `summary.json` counts generated, excluded, executed, completed, matched, mismatched,
  inconclusive, error and unexecuted cases, with source and compiler rejections counted
  separately within errors. Exit zero needs every requested case to match and every required
  coverage item; exhaustion, interruption and resource limits never pass.
- `cases/` and `results/` keep every case and a compact report, which is not an exact archive.
  Each finding keeps the complete original and reduced archives under `findings/` with
  `shrink.json`, for the single-case runner's `--replay`.
- A reduction candidate must keep the failure category, stage, disagreeing paths and each path's
  outcome and payload form, so a wrong return cannot shrink into a revert or a resource failure.
  Other genuine findings met while shrinking are kept separately. A reduction ends at its attempt
  limit, not at a proven minimum.

### Stateful cases and campaigns

```sh
lake build semanticStorageTool rustHullStorageScenario
.lake/build/bin/semantic-storage-tool generate 0 256 2 64 1000000 > STORAGE-CORPUS.json
python3 scripts/semantic-storage-differential.py --case CASE.json --output RUN
python3 scripts/semantic-storage-differential.py --replay RUN --output REPLAY
python3 scripts/semantic-storage-campaign.py --corpus scripts/semantic-storage-corpus.json \
  --output .upstream/semantic-storage-ci --seconds 600
python3 scripts/semantic-storage-campaign.py --seed 3 --nodes 384 --cases 4 --attempts 256 \
  --output .upstream/semantic-storage-search --seconds 600
```

- Every stateful case tool has `generate SEED NODES COUNT ATTEMPTS FUEL [VERSION]
  [TRANSACTIONS]`, `emit PLAN.json TRANSACTIONS.json [FUEL]`, `replay CASE.json [FUEL]`,
  `observe CASE.json BINDINGS.json [FUEL]` and `shrink CASE.json LIMIT [FUEL]`; `COUNT` counts
  scenarios. The runners and campaigns pick the profile's tool, Hull runner and rules from the
  case or manifest, and `--profile` selects one for a search.
- A case holds the original Core contracts, the source, the plan and the transactions, each with
  a stable `id`, and no expected result.
- `observe` runs the original contract through `ContractRuntime`. Bindings
  (`solcore-lean.storage-bindings.v1`, `solcore-lean.call-bindings.v1` for calls) carry the
  actual Anvil caller and contract addresses, which both Core paths use.
- Each invocation runs the same installed code with a fresh heap; only the committed world passes
  to the next transaction.
- The EVM path reads return bytes from each mined transaction's trace and slots with
  `eth_getStorageAt` at the receipt's block. Anvil runs with `--steps-tracing`: a failed receipt
  is a revert only when its trace ends in `REVERT` and no resource error applies, so out-of-gas,
  fuel exhaustion and exceptional failure never match as a rollback. An uncertain submission is
  never retried.
- A pass needs agreement on the initial state and on status, return bytes and every observed
  field after every transaction, on all three path pairs. A later resource failure never erases
  an observed prefix mismatch.
- The summary counts scenarios apart from transactions observed, transactions completed on all
  three paths and matched prefixes; shrink executions are not counted.

### Suites, reducer check and harness tests

`scripts/semantic-suite.py` runs the campaigns of every profile in turn with shared limits
([fixed and random suites](SEMANTIC_CI.md#fixed-and-random-suites)); repeat `--profile` to select:

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-primitives \
  --backend sonatina-o0 --output .upstream/semantic-primitives-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-primitives \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-primitives-random
```

A test adapter changes a copied observation only after all three real executions agree:

```sh
python3 scripts/semantic-campaign.py --seed 78 --nodes 32 --cases 1 --attempts 1 \
  --test-perturb-path rustEvm --shrink-attempts 8 --output .upstream/semantic-reducer-test
python3 scripts/semantic-campaign.py \
  --case .upstream/semantic-reducer-test/findings/synthetic/0000/reduced/case.json \
  --test-perturb-path rustEvm --shrink-attempts 0 --output .upstream/semantic-reducer-replay
python3 scripts/semantic-storage-campaign.py --case CASE.json \
  --test-perturb-path importedHull --test-transaction-id tx-1 --test-field storage:1 \
  --shrink-attempts 12 --output .upstream/semantic-storage-reducer --seconds 600
```

- The first command exits nonzero by design. Synthetic findings are stored apart from genuine
  ones, the changed observation exists only in `analysis.json`, and without the adapter the
  reduced case's three results still match. This tests detection, preservation and reduction; it
  is no evidence of a compiler bug.
- The stateful campaigns' `--test-field` takes `output`, `storage:SLOT`, `stray` and, where
  observed, `log` or `balance`. A candidate that removes the selected transaction cannot keep the
  synthetic finding. `output` flips the low bit of the last Word of any output of whole Words, so
  tuple, `bytes` and enum returns reduce too.

```sh
python3 scripts/test-semantic-differential.py
python3 scripts/test-semantic-campaign.py
python3 scripts/test-semantic-storage-differential.py
python3 scripts/test-semantic-storage-campaign.py
python3 scripts/test-semantic-call-differential.py
python3 scripts/test-semantic-call-campaign.py
python3 Tests/scripts/test-semantic-corpus.py
python3 scripts/test-source-synthesis-rust.py
```

- The runner and campaign tests cover the protocol, real child-process timeouts and output
  limits, and archive tampering; they do not show that the three paths ran.
- The corpus validators in `Tests/scripts/` check deterministic materialization, native Core
  execution, replay and coverage, without an EVM.
- `test-source-synthesis-rust.py` checks 27 explicit operation, boundary and scope cases and 12
  generated cases: each source passes the public Rust checking pipeline, and its imported Hull
  returns exactly the ABI encoding of the original Core result. It runs no EVM. Prepare the
  checked Hull exporter first ([RUST_PARITY.md](RUST_PARITY.md)).
- Each `scripts/test-source-*-rust.py` runs a profile's external regression cases on the real
  paths, then exact replay. `Tests/Main.lean` registers the emitter and case-tool regressions.

Keep the regression cases and replay metadata that explain a finding. Remove disposable exports
and logs once the results are recorded.

## Profiles

The suite's 66 profiles, from `scripts/semantic-suite.py`. Every pure and storage-family
profile runs on all three backends. `stateful-calls` and `stateful-forwarded-value` compile both
contracts from one source, which the Yul exporter does not admit, so they run on Sonatina only.

| Profile | Family | Backends | Content |
| --- | --- | --- | --- |
| `closed-g0` | pure | O0, O2, Yul | A closed G0 Word expression, no runtime input |
| `runtime-word` | pure | O0, O2, Yul | A G0 expression with one literal abstracted into the runtime Word |
| `runtime-primitives` | pure | O0, O2, Yul | `runtime-word` with raw `std.opcodes` division, shifts, `byte`, `signextend`, `exp`, `clz` and modular operations |
| `runtime-assembly` | pure | O0, O2, Yul | The primitive functions written as inline Yul, in three forms |
| `runtime-call-graphs` | pure | O0, O2, Yul | One to three helpers in an arbitrary call graph |
| `runtime-functions` | pure | O0, O2, Yul | One to three named Word helpers called in a chain |
| `runtime-mutation` | pure | O0, O2, Yul | Helpers with private mutable Word locals |
| `runtime-aggregates` | pure | O0, O2, Yul | Internal pairs, sums and two-way matches |
| `runtime-aggregate-call-graphs` | pure | O0, O2, Yul | Pairs, sums and matches composed with helper calls |
| `runtime-loops` | pure | O0, O2, Yul | A bounded `while` loop over an aggregate step |
| `runtime-call-graph-loops` | pure | O0, O2, Yul | The bounded loop over a call-graph step |
| `runtime-nested-loops` | pure | O0, O2, Yul | A bounded loop inside a bounded loop |
| `runtime-recursion` | pure | O0, O2, Yul | Tail, non-tail and mutual recursion to an input-chosen depth |
| `runtime-loop-closures` | pure | O0, O2, Yul | Closures created in loop bodies over loop-carried locals |
| `runtime-recursive-loops` | pure | O0, O2, Yul | Loops inside recursive frames |
| `runtime-assembly-loops` | pure | O0, O2, Yul | A call-graph loop as a Yul `for` loop with Yul functions |
| `runtime-assembly-memory` | pure | O0, O2, Yul | A primitive step through memory in inline Yul, with `keccak256` |
| `runtime-generics` | pure | O0, O2, Yul | A polymorphic selector at Word, pair and sum |
| `runtime-closures` | pure | O0, O2, Yul | Word captures through source lambdas and a generic apply |
| `runtime-comptime` | pure | O0, O2, Yul | A `comptime<word>` constant combined with a runtime step |
| `runtime-modules` | pure | O0, O2, Yul | Four module files combining a constant, closures and generics |
| `runtime-enums` | pure | O0, O2, Yul | User-defined enums and `match` |
| `runtime-traits` | pure | O0, O2, Yul | One trait with constrained generic impls at Words, tuples, sums and enums |
| `runtime-trait-hierarchies` | pure | O0, O2, Yul | A subclass trait, a chain above it and a method-level generic |
| `runtime-memory-values` | pure | O0, O2, Yul | std `bytes`, slices and Word arrays in straight-line code and loops |
| `runtime-memory-calls` | pure | O0, O2, Yul | Memory values passed to, written by and returned from helpers |
| `runtime-revert-data` | pure | O0, O2, Yul | std `Error` values raised as revert data on input-dependent paths |
| `runtime-halts` | pure | O0, O2, Yul | The revert data plans with INVALID halts |
| `runtime-checked-arithmetic` | pure | O0, O2, Yul | Checked and `unchecked` arithmetic over `uint8` to `int256` |
| `runtime-shifts` | pure | O0, O2, Yul | `<<` and `>>` on Words and integers |
| `runtime-memory-arrays` | pure | O0, O2, Yul | `T[]` memory arrays, slices, grids, `memref` writes and a storage array |
| `runtime-array-abi` | pure | O0, O2, Yul | `T[]` and `calldata<T[]>` parameters and `T[]` results |
| `runtime-closure-captures` | pure | O0, O2, Yul | Closures that capture by value, with writes, rebinding and calls |
| `runtime-closure-factories` | pure | O0, O2, Yul | Functions and methods that make and return closures |
| `stateful-storage` | stateful | O0, O2, Yul | Two slots updated by an aggregate step |
| `stateful-storage-rollback` | stateful | O0, O2, Yul | The two-slot contract, reverting after its writes |
| `stateful-keyed-storage` | stateful | O0, O2, Yul | Writes at a key, its wrapping successor and a counter |
| `stateful-dynamic-array` | stateful | O0, O2, Yul | A `uint256[]` argument of up to three elements |
| `stateful-logs` | stateful | O0, O2, Yul | Event logs with zero to four topics |
| `stateful-call-value` | stateful | O0, O2, Yul | Nonzero call value and the contract's balance |
| `stateful-bytes` | stateful | O0, O2, Yul | A `bytes` argument of up to 64 bytes |
| `stateful-long-bytes` | stateful | O0, O2, Yul | A `bytes` argument of up to 256 bytes |
| `stateful-nested-array` | stateful | O0, O2, Yul | A `uint256[][]` argument of up to three rows of two |
| `stateful-mapping` | stateful | O0, O2, Yul | A mapping whose entries live at Keccak-256 slots |
| `stateful-ledger` | stateful | O0, O2, Yul | Mapping entries keyed by three senders |
| `stateful-malformed-calldata` | stateful | O0, O2, Yul | The dynamic-array contract with malformed calldata |
| `stateful-malformed-nested-array` | stateful | O0, O2, Yul | The nested-array contract with malformed calldata |
| `stateful-malformed-bytes` | stateful | O0, O2, Yul | The long-bytes contract with malformed calldata |
| `stateful-methods` | stateful | O0, O2, Yul | Two to four external methods over shared slots |
| `stateful-storage-loops` | stateful | O0, O2, Yul | A loop reading and writing one slot per iteration |
| `stateful-keccak-loops` | stateful | O0, O2, Yul | A loop over mapping entries that logs every iteration |
| `stateful-assembly-storage-loops` | stateful | O0, O2, Yul | The storage loop with its storage accesses in inline Yul |
| `stateful-assembly-keccak-loops` | stateful | O0, O2, Yul | The Keccak loop with hashing, storage and logs in inline Yul |
| `stateful-adt-storage` | stateful | O0, O2, Yul | Enum and struct values in fields and behind mapping keys |
| `stateful-tuple-returns` | stateful | O0, O2, Yul | A static tuple of two to four Words returned |
| `stateful-bytes-returns` | stateful | O0, O2, Yul | A `bytes` value of up to 64 bytes returned |
| `stateful-enum-returns` | stateful | O0, O2, Yul | A user enum of two to four constructors returned |
| `stateful-enum-arguments` | stateful | O0, O2, Yul | A user enum argument, canonical or malformed |
| `stateful-enum-array-arguments` | stateful | O0, O2, Yul | A calldata array of up to three enums and two indices |
| `stateful-array-returns` | stateful | O0, O2, Yul | std's encoding of a memory array returned |
| `stateful-constructor-arguments` | stateful | O0, O2, Yul | Constructor parameters, canonical or malformed |
| `stateful-calls` | stateful, call | O0, O2 | A parent calling a child, with child and root rollback |
| `stateful-forwarded-value` | stateful, call | O0, O2 | A parent forwarding call value to a child |
| `stateful-call-returns` | stateful, call | O0, O2, Yul | A parent decoding a child's tuple, `bytes` or enum return data |
| `stateful-call-sequences` | stateful, call | O0, O2, Yul | Two or three calls in one method, reading return data around each |
| `stateful-call-branches` | stateful, call | O0, O2, Yul | Zero to three calls in branches and loops |

Outside the suite, `scripts/semantic-fixtures.py` compares the pinned end-to-end fixtures across
the compiled paths, without original Core
([pinned fixtures across paths](#compare-the-pinned-end-to-end-fixtures-across-paths)).

## Generation and campaign mechanics

### G0 generator revisions

G0 generates closed, checked Word expressions. Its four replay revisions share the same
`lcg64-v1` draws, and a case records its revision in `generatorVersion`. The primitive profile
records `core-primitives-v1/` followed by the revision there, and the plain revision in
`baseGeneratorVersion`.

| Revision | `generatorVersion` | Used by |
| --- | --- | --- |
| v1 | `core-g0-v1/lcg64-v1` | fixed corpora, imported programs, the case tool without a version |
| v2 | `core-g0-v2/lcg64-v1` | `--g0-version` for the pure and stateful profiles |
| v3 | `core-g0-v3/lcg64-v1` | random generation of every stateful step; `--g0-version` for the pure profiles |
| v4 | `core-g0-v4/lcg64-v1` | random generation of the seventeen G0-based pure profiles |

The seventeen are `closed-g0`, `runtime-word`, `runtime-primitives`, `runtime-assembly`,
`runtime-assembly-memory`, `runtime-functions`, `runtime-mutation`, `runtime-aggregates`,
`runtime-loops`, `runtime-nested-loops`, `runtime-recursion`, `runtime-recursive-loops`,
`runtime-loop-closures`, `runtime-generics`, `runtime-closures`, `runtime-comptime` and
`runtime-modules`. The other pure profiles do not use G0 revisions.

- **v1** takes each choice as the raw LCG state modulo its bound, so a literal's edge decision
  depends on its position in the stream. It stays bit for bit, because the fixed corpora
  regenerate from their seeds.
- **v2** passes each state through the SplitMix64 finalizer and takes the upper 32 bits modulo
  the bound, which separates consecutive seeds' streams and makes operator choices uniform. A
  literal is an edge or a random Word with one half each. The edge bank holds 0, 1, 2, 3, 7, 8,
  30, 31, 32, 63, 64, 127, 128, 255, 256, 257, 2^16−1, 2^16, 2^32−1, 2^32, 2^64−1, 2^64, 2^128−1,
  2^128, 2^160−1, 2^192, 2^248, 2^255−1, 2^255, 2^255+1, 2^256−2 and 2^256−1: shift counts, byte
  and sign-extension indices, masks, limb boundaries, the address mask and the int256 limits,
  with their neighbours.

#### Revision three: swarm masks

v3 is v2's grammar restricted by a swarm mask drawn once per case.

- The mask covers the 26 operators and non-leaf forms: Bool and Word negation, leading zeros,
  the nineteen binary operators including the three comparisons, `addmod`, `mulmod`, `let` and
  `if`. Literals and locals always stay available.
- Each feature has its own bit of one mixed, domain-separated SplitMix64 draw from the case seed,
  so about half are enabled. Every G0 program of a case, such as each helper and a comptime
  constant, uses the same mask.
- A form is drawn as in v2. Only a disabled form causes a second draw among the enabled non-leaf
  forms, so leaves keep v2's probability, and with the full mask v3 is v2. Reason: falling to a
  leaf instead made programs end early, with a quarter fewer operators.
- The case records the enabled features in `provenance.swarmMask`. Replay requires the mask of a
  v3 case, checks a seeded case's mask against its seed and rejects a mask on another revision.
  A reduction copies its parent's mask.
- Random campaigns have no coverage requirements of their own, so a mask cannot fail a run on
  coverage.

#### Revision four: masks within the emitter

v4 restricts the case's v3 mask to the G0 features the profile's emitter renders. Each emitter
declares them from its renderer's operator predicates (`featureSupport`), and a registered Lean
test checks that every catalog feature emits through every pure emitter exactly when declared.

| Renderer | Features | Programs |
| --- | --- | --- |
| Scalar | Bool and Word negation; add, sub, mul, and, or, xor, `==` and `>`; `let` and `if` (12 of 26) | `closed-g0`, `runtime-word`, `runtime-functions`, `runtime-mutation`; comptime and module constants |
| Primitive, call-graph and aggregate | all 26 | `runtime-primitives`, `runtime-aggregates`, `runtime-loops`, `runtime-generics`, `runtime-closures`; comptime and module steps |
| Inline Yul, in each of its three forms and as a step over memory | all 26 | `runtime-assembly`, `runtime-assembly-memory` |

- Where the emitter renders every feature, v4 is v3 apart from its version. A comptime or module
  case records its step's unrestricted mask, and its constant uses the scalar restriction.
- When the restriction removes every operator the mask enabled, the case uses the emitter's whole
  feature set, so it never draws programs of leaves, `let` and `if` alone; under the scalar
  renderer that happens for about one seed in a thousand.
- A v4 case records its effective mask, and replay rejects a mask outside the profile's features.
- The stateful tools parse versions only up to v3 and reject v4; the pure case tool accepts all
  four.
- Reason: under v3 most scalar-profile programs contained operators the scalar emitter rejects,
  and the identity `f(x) = x`, which every one-leaf program becomes, was most of the accepted
  `runtime-word` functions. Over the first 256 accepted functions of each profile, v4 left no
  unsupported-operator exclusion.

**Selecting a revision.** The G0-based generation commands take an optional version after
`FUEL`. Without one they generate v1, so fixed manifests regenerate unchanged; an unknown version
is rejected. `replay` uses the recorded revision, and `shrink` gives each reduction its parent's.
`semantic-campaign.py` passes v4 in random mode, and `--g0-version` selects another revision.
With `--corpus` it passes the manifest's version and with `--case` the saved case's, refusing a
disagreeing `--g0-version`. The summary records `configuration.g0Version` and
`generation.generatorVersions`. The stateful campaigns generate random steps with v3
([stateful conventions](#stateful-conventions)).

### Seeded runtime inputs

Random campaigns of the runtime-input profiles, every pure profile except `closed-g0`, run each
accepted function at its boundary inputs and then at four inputs derived from the case seed;
fixed corpora keep the boundary inputs alone. The four come from a SplitMix64 stream that starts
at the case seed XOR a fixed domain constant, five outputs each:

1. a full random 256-bit Word;
2. a random Word whose bit width is uniform from 1 to 256;
3. a small value below 512;
4. the two's-complement negation of another uniform-width value.

- A seeded input can coincide with a boundary input. The admission filters use the boundary
  inputs only.
- The generated origin records `"inputSelection": "seeded-inputs-v1/splitmix64"`, and
  `inputIndex` counts the boundary inputs first; no field means the boundary inputs alone.
  Replay recomputes the inputs and rejects a seeded index without a selection, an unknown
  selection or a changed input. A reduction keeps its input as data.
- The generation commands take the selection after `FUEL`, in either order with a G0 version:
  `input-generate SEED NODES COUNT ATTEMPTS FUEL [VERSION] [seeded-inputs-v1/splitmix64]`.
- The campaign passes it in random mode, and `--input-selection boundary` returns to the boundary
  inputs. A corpus refuses the seeded selection, and `--case` keeps the saved case's. The summary
  records `configuration.inputSelection` and `generation.inputSelections`.

Inputs per function, from `semantic-campaign.py`:

| Seeded (boundary) | Profiles |
| --- | --- |
| 8 (4) | `runtime-word`, `runtime-functions`, `runtime-mutation`, `runtime-aggregates`, `runtime-generics`, `runtime-closures`, `runtime-comptime`, `runtime-modules` |
| 10 (6) | `runtime-loops`, `runtime-call-graph-loops`, `runtime-assembly-loops`, `runtime-nested-loops`, `runtime-recursive-loops`, `runtime-loop-closures` |
| 11 (7) | `runtime-recursion` |
| 12 (8) | `runtime-primitives`, `runtime-assembly`, `runtime-assembly-memory`, `runtime-call-graphs`, `runtime-aggregate-call-graphs`, `runtime-enums`, `runtime-traits`, `runtime-trait-hierarchies`, `runtime-memory-values`, `runtime-memory-calls`, `runtime-revert-data`, `runtime-halts`, `runtime-checked-arithmetic`, `runtime-shifts`, `runtime-memory-arrays`, `runtime-array-abi`, `runtime-closure-captures`, `runtime-closure-factories` |

**Whole functions.** `--cases` counts inputs, so a run's last function may lose inputs;
`--functions N` instead generates N accepted functions with all their inputs.
- The case tool returns at most 1,024 cases, so N is at most 128, 102, 93 or 85 with seeded
  inputs, by the rows above (256, 170, 146 or 128 with boundary inputs).
- Without `--attempts`, the budget is at least 16 candidates per function, up to the case tool's
  10,000, in the campaign and in the suite.
- The campaign refuses `--functions` with `--cases`, a corpus, a saved case or `closed-g0`. The
  summary records `configuration.functions`, `generation.requestedFunctions` and
  `generation.inputsPerFunction`.

**Output limit.** A case-tool response is limited to 2 MiB, so random generation takes as many
requests as it needs. The first asks for every case. A response over the limit is asked again
from the same seed for half as many whole functions, and each later request starts at the seed
after the previous request's last attempt, modulo 2^64 as the case tool's `Seed.ofNat` reduces
it. The merged cases, exclusions, attempts and status equal one request's. Only a function whose
cases alone exceed the limit stops, as an inconclusive `output-limit`. The summary records
`generation.requests` and `generation.outputLimitRetries`, and
`Tests/scripts/test-semantic-chunked-generation.py` checks the merge byte for byte.

### Boundary identities

Random campaigns of the runtime-input profiles whose functions can be identities apply the
acceptance filter `exclude-boundary-identity-v1`. After the profile's own filters, it excludes a
function that returns each of its boundary inputs unchanged (reason `every boundary input
returned itself`, code `boundary-identity`). Reason: such a function exercises only each path's
ABI decoding and return, yet costs a compilation and every input's execution. It decides on the
boundary results alone, so a kept function can still return a seeded input unchanged.

| Identity filter | Profiles |
| --- | --- |
| applied | `runtime-word`, `runtime-primitives`, `runtime-assembly`, `runtime-assembly-memory`, `runtime-functions`, `runtime-mutation`, `runtime-aggregates`, `runtime-closures`, `runtime-comptime`, `runtime-modules`, `runtime-call-graphs`, `runtime-aggregate-call-graphs`, `runtime-enums`, `runtime-traits`, `runtime-trait-hierarchies`, `runtime-memory-values`, `runtime-memory-calls`, `runtime-revert-data`, `runtime-checked-arithmetic`, `runtime-shifts`, `runtime-memory-arrays`, `runtime-array-abi`, `runtime-closure-captures`, `runtime-closure-factories` |
| not needed | `runtime-loops`, `runtime-call-graph-loops`, `runtime-assembly-loops`, `runtime-loop-closures`: a positive-trip boundary input must already change; `runtime-nested-loops`, `runtime-recursion`, `runtime-recursive-loops`: some boundary input must change |
| not needed | `runtime-generics`: input 0 returns the result of input 1 or its successor, so it never returns both 0 and 1 |
| not needed | `runtime-halts`: every accepted plan halts at a boundary input |

- The filter is versioned on its own, not as a G0 revision. Reason: acceptance belongs to each
  profile's case module, and only generated cases pass filters; imported cases and reductions
  never do, and a reduction may itself be an identity.
- A filtered origin records `"acceptance": "exclude-boundary-identity-v1"`. Replay applies it
  again: a saved identity that claims it is refused with the exclusion reason, an unknown value
  with `unsupported acceptance filter`. Reductions record no filter.
- The generation commands of the profiles that apply it take it after `FUEL`, in any order with a
  G0 version and an input selection; the others refuse it. The campaign passes it in random mode;
  `--acceptance profile` returns to the profile's own filters. A corpus refuses it, and `--case`
  keeps the saved case's. The summary records `configuration.acceptance` and
  `generation.acceptances`.
- Generation without the option is byte for byte as before the filter. The stateful profiles are
  untouched.

### Raw primitives in aggregate-based step functions

Since emitter version 2, `AggregateRenderer` renders the fourteen raw primitives of the
[runtime operation mappings](#runtime-operation-mappings) in checked aggregate step functions:
leading zeros, unsigned and signed division and remainder, signed greater-than, the three shifts,
byte selection, exponentiation, sign extension, `addmod` and `mulmod`. They were operator
exclusions before.

- Each call follows the mappings, its operands snapshotted into fresh locals as the call-graph
  renderer does.
- The original operations (`+ - * & | ^ == > ! ~`) keep their exact text, so a program without a
  raw primitive emits byte-identical source. Aliases such as
  `import { div as sc_div, ... } from std.opcodes;` are imported only when a step uses one.
- The eleven profiles that used the renderer then moved their emitter and profile versions to
  `v2`: `runtime-aggregates`, `runtime-loops`, `runtime-generics`, `runtime-closures`, the steps
  of `runtime-comptime` and `runtime-modules`, and the storage, rollback, parent/child call, keyed
  storage and dynamic-array profiles. Older saved cases fail with `profileVersion changed`
  instead of being re-emitted.
- Unchanged: `ScalarRenderer`, which the emitter proof unfolds, with its users `closed-g0`,
  `runtime-word`, `runtime-functions` and the comptime and module constants; and
  `MutationRenderer` (`runtime-mutation`).
- The affected fixed corpora gained entries covering all fourteen primitive features. An
  independent Python evaluator with the EVM primitive semantics computed the new keyed and
  dynamic-array histories.

### Shared compilation in campaigns

Checked Hull export and code-image export read a case's source files, not its input, and take
most of a case's time. A pure or storage campaign therefore compiles each distinct source once
per backend.

- The compilation identity is the SHA-256 of the case's own source files (all four for modules),
  the backend and optimization, every standard-library source, both compiler binaries and their
  build receipts, the four exporter files, the runner and the Python interpreter. Yul adds solc's
  digest and version and the Yul exporter and transport.
- Equal identities share one compilation in `.work/compilations/DIGEST/`, byte-identical sources
  of two seeds included. Each case copies the outputs into its own run directory and checks their
  digests, so its archive stays self-contained, and records `compilation`. A reusing case lists
  the shared processes with `reused: true`.
- Every case still runs its own direct Core replay, deployment, EVM call and Hull execution.
- A rejection or crash stays with its compilation and counts for every case with that source; a
  timeout, output limit, interruption or adapter failure is not kept. At most eight compilations
  are kept, the least recently used deleted first.
- Reduction candidates and exact replay compile on their own. The summary records
  `distinctSources`, `compiled` and `reused`.

A compilation takes about four seconds, and a case that reuses one 0.6 to 0.8 seconds.

### Per-case overhead and the fixed suite's budget

Campaigns also avoid repeated work that does not depend on the case.

- A fixed pure corpus generates each recipe once for all its entries' inputs
  (`corpus.generationRequests`).
- Tool and compiler files are hashed once per campaign while their path, device, inode, size and
  modification and status-change times are unchanged. A write always moves the status-change
  time, so a reused digest is that of the same bytes. Version outputs are reused the same way.
- The suite's disk check walks only the running profile's folder and still stops a profile about
  0.11 seconds after the output reaches the limit less the 8 MiB reserve. It reads the process
  table at every check and stop, in-process from `sysctl(KERN_PROC_ALL)` on macOS and with `ps`
  elsewhere, so it still stops a descendant whose parent exited.
- The nine pure profiles whose cases carry Core references of thousands of nodes keep their case
  files as compact JSON: `runtime-assembly-memory`, `runtime-traits`,
  `runtime-trait-hierarchies`, `runtime-memory-values`, `runtime-memory-calls`,
  `runtime-memory-arrays`, `runtime-array-abi`, `runtime-closure-captures` and
  `runtime-closure-factories`. Digests and replay are unchanged.

The budget: with these changes the default fixed suite of fifty-five profiles fitted the CI job's
7,200 seconds and 1 GiB on Sonatina O0 and on Yul. The profiles added since push the O0 fixed
suite past 7,200 seconds, so split the fixed job by `--profile`
([fixed and random suites](SEMANTIC_CI.md#fixed-and-random-suites)).

## Pure profiles

Each pure case calls one function of one runtime Word. Rules shared by the pure profiles:

- An accepted function supplies its boundary inputs in order, then, in random mode, four
  [seeded inputs](#seeded-runtime-inputs). `--attempts` counts functions, graphs or plans, and
  `--cases` counts inputs.
- Generation excludes a function whose boundary results all agree, or one that exhausts fuel;
  each section adds its profile's own filters. Imported and reduced functions may be constant.
- Replay checks the original Core argument, ABI calldata, function, source and versioned
  provenance, and recomputes every observation. A plan-based case keeps its plan and the applied
  original Core `program`, whose exact correspondence native admission checks for every origin,
  and a generated plan must be its seed's.
- Every reduction is resealed by the Core checker and strictly smaller. It keeps helper
  declarations and typed and payload binders, and records its parent.
- Each profile has the native commands `<name>-generate SEED NODES COUNT ATTEMPTS FUEL
  [options]` and `<name>-emit PLAN.json INPUT [FUEL]`, listed in `semantic-campaign.py`. The
  names follow the profile: `enum-generate` for `runtime-enums`, `hierarchy-generate` for
  `runtime-trait-hierarchies`, and `input-generate` for `runtime-word`.
- Run a profile with `semantic-campaign.py --profile P --functions 8` (random) or with
  `--corpus scripts/<stem>-corpus.json` (fixed), the stem being the one in `semantic-suite.py`.
  Most profiles have their own validator `Tests/scripts/test-semantic-<name>-corpus.py`;
  `Tests/scripts/test-semantic-corpus.py --manifest MANIFEST` validates the earlier manifests.
- Coverage requirements are those of the fixed corpus. They count only cases that matched on all
  three paths and describe plans, not measured traces.
- Unless a section names a finding, the profile's fixed corpus matched on all three paths.

### Compare closed G0 programs

`closed-g0` emits a checked, closed G0 Word program with Boolean subexpressions, local Word
bindings, conditionals, Boolean and Word negation, addition, subtraction, multiplication,
bitwise and, or and xor, equality and unsigned greater-than. `SynthesizedG0.run()` takes no input
and returns one ABI `uint256`. The Core reference is the program itself.

- Fixed corpus `scripts/semantic-corpus.json`: sixteen seed and node-budget pairs with their
  expected versions and AST features. It requires every enabled operation, bindings, branches and
  the Word literals zero, one, maximum and the high bit.
- Caveat: Rust may fold the whole computation, so this profile covers source features, not the
  arithmetic opcodes.

### Compare functions with runtime inputs

`runtime-word` abstracts one Word literal of a G0 expression into a checked Word-to-Word lambda,
without capturing locals. Original Core applies the lambda to the recorded Word, and the source
takes it through `SynthesizedInput.run(uint256)`, so a new input never changes the source.

- Boundary inputs: zero, one, the maximum Word and the high bit. Generation fuel failures appear
  in `generationResourceExclusions`, a subset of `excluded`.
- Fixed corpus `scripts/semantic-input-corpus.json`: identity, unsigned boundary branches, nested
  local scopes and generated bodies, with no claim of the richer M4 features or measured EVM
  opcode coverage. `requiredInputs` is met only by inputs whose three executions agree;
  `requiredWordLiterals` measures literals in the Core AST and is no input coverage.
- `python3 scripts/test-source-input-rust.py` runs two source functions at the four inputs and
  replays a saved run.

### Compare the extended Word primitives

`runtime-primitives` keeps the checked Word-to-Word function and imports fourteen raw
`std.opcodes` functions as explicit aliases: unsigned and signed division and remainder, signed
greater-than, shifts, byte selection, sign extension, exponentiation, leading-zero count and
modular addition and multiplication. The mappings below give each one's operand order and
boundary rule.

- Boundary inputs: 0, 1, 2, 255, 256, the maximum Word, the high bit and the high bit minus one.
- Default budget 96 nodes and 512 attempts, admitted range 8 to 512.
- Fixed corpus: 81 hand-specified cases, requiring all fourteen new AST operators.

<a id="3-missing-runtime-operation-mappings"></a>

#### Runtime operation mappings

The profiles whose step functions use `AggregateRenderer` import the same aliases, only when they
use them. The table describes the raw functions, not the public convenience wrappers of similar
names, which are not interchangeable with them.

| Core operation | Raw source call | Boundary rule |
| --- | --- | --- |
| `wordDiv(a,b)` | `div(a,b)` | Zero divisor returns zero. |
| `wordMod(a,b)` | `mod(a,b)` | Zero divisor returns zero. |
| `wordSdiv(a,b)` | `sdiv(a,b)` | Signed two's-complement division, including minimum / -1. |
| `wordSmod(a,b)` | `smod(a,b)` | Signed remainder follows the dividend; zero divisor returns zero. |
| `wordSgt(a,b)` | `tobool(sgt(a,b))` | Convert raw Word 0/1 to the Core Boolean result. |
| `wordShl(v,n)` | `shl(n,v)` | Reverse only the captured arguments; shifts at least 256 return zero. |
| `wordShr(v,n)` | `shr(n,v)` | Same argument reversal and large-shift rule. |
| `wordSar(v,n)` | `sar(n,v)` | Same reversal; large shifts fill with the sign bit. |
| `wordAddMod(a,b,m)` | `addmod(a,b,m)` | Do not truncate the intermediate addition; modulus zero returns zero. |
| `wordMulMod(a,b,m)` | `mulmod(a,b,m)` | Do not truncate the intermediate product; modulus zero returns zero. |
| `wordClz(v)` | `clz(v)` | Zero returns 256. |
| `wordByte(i,v)` | `byte(i,v)` | Index-first on both sides; indices at least 32 return zero. |
| `wordSignExtend(i,v)` | `signextend(i,v)` | Index-first on both sides; indices at least 32 preserve the value. |
| `wordPow(b,e)` | `exp(b,e)` | Modular exponentiation; zero exponent returns one, including 0^0. |

- Each operand is evaluated into a fresh temporary, in original Core order, before the call.
- Public `std.addmod` and `std.mulmod` reject a zero modulus, so they cannot replace the raw
  aliases.
- Byte selection and sign extension take the index first on both sides and are not reversed.
- Core's exponent uses repeated modular squaring, so a Word exponent never builds the unbounded
  power.

### Compare inline Yul

`runtime-assembly` renders the functions of `runtime-primitives` partly or wholly as inline Yul
in `assembly { }` blocks, which reach the compiler's inline-assembly path: Yul parsing, Solcore
locals inside `assembly`, builtin resolution and lowering to Hull. The Core reference is the
primitive profile's function for the same seed, budget and revision.

A plan (`solcore-lean.assembly-plan.v1`) has a `form` drawn from a hash of the seed:
- `switch`: the whole body is one block assigning `sc_out`, each Core `if` a Yul `switch` whose
  `case 0` computes the else branch;
- `if`: the same, each Core `if` a Yul local holding the condition and two Yul `if`s;
- `operations`: Solcore `let`, `if`, literals and `!`, with every other operation in its own
  block; a comparison becomes a Bool through std's `tobool`.

- Yul never reads a Solcore Bool. The builtins cover all 26 G0 features, so v4 equals v3. No
  emitter proof covers `SynthesizedAssembly.run(uint256)`.
- Generation, inputs, exclusions and reductions are `runtime-primitives`'; a reduction keeps its
  parent's form. `assemblyRequirements` declares the `forms` and `formFeatures`.
- Fixed corpus: the primitive corpus's 34 distinct functions in three groups combined by a
  balanced XOR tree, in every form at the eight inputs: 72 cases covering all 29 AST features.
- Decision: the 81 primitive cases in every form exceeded the 900-second profile limit on Yul, and
  generated functions that shift by a constant count of at least 2^64 crash Sonatina O0 code-image
  export. The corpus avoids that construct; random campaigns still generate it.
- Known finding: such random functions crash Sonatina O0 code-image export with `Integer overflow
  when casting to usize`, on O0 and on Yul, which imports O0 images. A reduction kept a left
  shift of the constant 0 by a constant count far above 256. Recorded locally, not investigated.

### Compare directly generated call graphs

`runtime-call-graphs` generates typed Word and Bool expressions with the runtime parameter in
scope. One to three helpers can call any earlier helper, and the entry and arguments follow no
fixed chain. Local bindings, conditionals and all scalar primitives are admitted. The Core checker
seals the whole graph, and the original Core application is the oracle.

- Default budget 192 nodes and 1,024 attempts, admitted 13 to 512. Small budgets can exhaust
  generation, because the entry must contain a call.
- Fixed corpus: 56 cases with hand-specified Core results, requiring helper counts one to three,
  the primitive profile's eight inputs and nine structures: skipped helpers, multiple callees,
  shared callees, nested calls, calls in branches and in local bindings, a diamond, calls in
  predicates and primitive operands (`callShapeCoverage`).

### Compare acyclic named functions

`runtime-functions` adds one to three named Word helpers, each able to call earlier ones, and an
entry that receives the ABI Word. The Core program keeps the chain of helper lambdas and applies
the entry closure to the input; the source uses top-level functions and
`SynthesizedFunctions.run(uint256)`. Recursive or escaping function values and references to host
bindings are out of scope.

- Generated graphs call every earlier helper in a chain; imported graphs can share callees, as in
  the diamond fixture. Node limits cover the whole application.
- Reduction keeps the helper count: it removes calls and simplifies bodies but never deletes
  declarations. `matchedHelperCounts` counts declarations, not runtime calls.
- `python3 scripts/test-source-function-rust.py` runs the external regression cases.

### Compare private mutable locals

`runtime-mutation` lets one to three acyclic helpers allocate private Word cells, read and update
them, and sequence Unit results through locals and branches. Cell aliases, escaping cells and
non-Word cells are excluded. The Core graph keeps real allocations, loads and stores; the source
uses mutable Word locals in `SynthesizedMutation.run(uint256)`.

- Versioned templates combine G0 scalar expressions with ordered stores, Unit branches, two
  independent cells and a load followed by a later update. Every read is captured before later
  effects. Default budget 192 nodes.
- A reduction may simplify a stored value or replace a store with Unit, but keeps its binder.
- Fixed corpus: 28 cases, requiring fourteen AST features, helper counts one to three and, in
  `recipeCoverage`, the four templates and update counts one to four.
- `python3 scripts/test-source-mutation-rust.py` checks read-before-write snapshots, independent
  cells and callee isolation.

### Compare internal pairs, sums and matches

`runtime-aggregates` admits internal `(word, word)` pairs, `sum<word, word>` values, projections
and two-way matches, with scalar operations, private Word cells and helpers, behind the Word ABI
`SynthesizedAggregates.run(uint256)`. Nested aggregate types, aggregate cells and escaping cell
values are out of scope. Raw primitives render as in
[the aggregate renderer](#raw-primitives-in-aggregate-based-step-functions); integer operations
remain exclusions.

- Pair operands evaluate left to right and keep their values across later writes; projections and
  sum scrutinees evaluate once. Reductions keep the payload markers and typed lets.
- Default budget 256 nodes.
- Fixed corpus: 44 cases, requiring eighteen AST feature kinds, helper counts one to three and the
  four templates.
- `python3 scripts/test-source-aggregate-rust.py` checks snapshots, single evaluation of
  projections and nested payload and helper effects.

### Compare aggregate compositions with call graphs

`runtime-aggregate-call-graphs` generates typed Word, Bool, pair and sum expressions directly,
with one to three helpers that may call any earlier one. Pairs, sums, projections, let-bound
aggregates, aggregate-valued branches and case expressions compose with calls in operands,
components, payloads, scrutinees and branches. Arguments, results and the ABI stay Words; private
cells and Unit values are out of scope.

- The source combines the call-graph renderer with the aggregate profile's tuple, sum and `match`
  forms. Default budget 192 nodes, admitted 13 to 512.
- An accepted graph needs an entry call and a call composed with an aggregate value or payload.
- Fixed corpus: 56 cases with expected Words computed outside Lean, requiring the 36 scalar and
  aggregate AST features and nine structures (`aggregateShapeCoverage`).
- Known finding: on O2 one random graph gave eight compiler crashes, a recorded upstream
  finding.

### Compare bounded loops

`runtime-loops` keeps a checked aggregate step graph and a mask. The source runs
`while (limit > counter)` with `limit = input & mask`, updating an accumulator through the step.
The Core reference captures the step closure once and runs a finite sequence of literal-ordinal
guards and accumulator stores; it does not reuse the source's counter.

- A plan (`solcore-lean.loop-plan.v1`) has a `stepProgram` and a `mask` of 0, 1, 3 or 7.
  Generation draws 1, 3 or 7 and needs a positive-trip input that changes its value.
- Boundary inputs: 0, 1, 3, 7, the maximum Word and the high bit. Default budget 384 nodes.
- Fixed corpus: 60 cases, requiring masks and iterations 0, 1, 3 and 7 (`loopRequirements`).
- `python3 scripts/test-source-loop-rust.py` checks zero and positive iterations, fresh
  helper-local cells per iteration and Word wrap.

### Compare bounded loops over call graphs

`runtime-call-graph-loops` uses a directly generated scalar call graph as the loop's step. The
aggregate DAG checker and the loop plan reseal it, and the finite ordinal-guard reference is
reused with no new evaluator. The source emits the helpers, then the entry as `sc_step`, inside
the same `while` wrapper.

- Generation subtracts the mask's measured wrapper from the budget, then generates the step with
  the call-graph grammar. Default budget 256 nodes, admitted 39 to 512; the mask-seven wrapper
  alone needs 111. Reductions never raise the mask.
- Fixed corpus: eleven plans at six inputs, 66 cases, with expected Words computed outside Lean
  from EVM Word semantics. It requires the thirty scalar features, the nine call shapes, and
  masks and iterations 0, 1, 3 and 7.

### Compare nested bounded loops

`runtime-nested-loops` runs a bounded loop whose body runs a second bounded loop around the step.
A plan (`solcore-lean.nested-loop-plan.v1`) has an `outerMask` and an `innerMask` of 0, 1 or 3 and
an `innerBound` that reads the input, the counter or the accumulator.

- From `acc = x`, the wrapper runs `x & outerMask` outer iterations. Each sets the inner bound
  (`x & innerMask`, `(i + 1) & innerMask` or `acc & innerMask`) and calls `acc = sc_step(acc)`
  once per inner iteration: at most nine step calls.
- The Core reference unrolls both loops' guards over one accumulator cell, with no counter cell;
  no emitter proof covers `SynthesizedNestedLoops.run(uint256)`.
- `provenance.iterations` records each outer iteration's inner trip count, from the plan, the
  input and, for the accumulator bound, the step's Core results. It is not a measured trace.
- Boundary inputs: 0, 1, 2, 3, the maximum Word and the high bit. Default budget 384 nodes.
- Fixed corpus: twelve plans, one per shape, 72 cases, requiring outer iterations 0 to 3, inner
  trip counts 0 to 3 and total step calls 0, 1, 2, 3, 4, 6 and 9.

### Compare bounded recursion

`runtime-recursion` calls a recursive source function, or two that call each other, to the depth
`d = x & depthMask` of the input `x`, over an aggregate step. The contract returns `f(d, x)`,
where `f(0, acc) = acc`:

- `tail`: `sc_rec(d, acc) = sc_rec(d - 1, sc_step(acc))`;
- `nontail`: `sc_rec(d, acc) = sc_step(sc_rec(d - 1, acc)) + d`;
- `mutual`: `sc_even(d, acc) = sc_odd(d - 1, sc_step(acc))` and
  `sc_odd(d, acc) = sc_even(d - 1, acc + d)`, entered at `sc_even`.

- The Core reference unrolls the frames into ordinal guards over one accumulator cell, with no
  recursion and no counter. A Lean test compares it frame by frame with a recursive model of the
  source. No emitter proof covers `SynthesizedRecursion.run(uint256)`.
- A plan (`solcore-lean.recursion-plan.v1`) has the step, a `depthMask` of 0, 1, 3 or 7 and the
  `form`. Reductions may lower the mask or replace `nontail` or `mutual` by `tail`.
- Boundary inputs: 0, 1, 2, 3, 7, the maximum Word and the high bit. Default budget 384 nodes.
- Fixed corpus: nine plans, one per shape, 63 cases, requiring depths 0, 1, 2, 3 and 7.

### Compare composed control flow

Two profiles compose the control constructs above over an aggregate step generated as for
`runtime-loops`, with a default budget of 384 nodes. Neither emitter has a proof.

- `runtime-loop-closures` runs `x & m` iterations from `acc = x`. Every iteration creates a fresh
  closure capturing a loop-carried Word local, changes that local, then applies the closure. With
  `accumulator`, `f(a) = step(acc + a)` must hold the snapshot taken before `acc = acc + 1`; with
  `counter`, `f(a) = step(a) + c` must hold the counter before its increment and is applied
  through the generic `sc_apply` of `runtime-closures`. The Core reference unrolls the guards;
  each builds a Core lambda over an immutable Word snapshot.
- `runtime-recursive-loops` calls the recursion forms to depth `d = x & D`, and every frame of
  depth `e > 0` runs a loop of `e & I` iterations: at most three frames and six iterations. The
  Core reference unrolls the frames and their inner guards, with no recursion, loop or counter
  cell.
- Boundary inputs: 0, 1, 3, 7, `2^256 - 1` and `2^255` for loop closures; 0, 1, 2, 3, `2^256 - 1`
  and `2^255` for recursive loops.
- Fixed corpora from G0 revision one: loop closures 48 cases with all six shapes and iteration
  counts 0, 1, 3 and 7; recursive loops 78 cases with all twelve shapes, depths 0 to 3 and total
  iterations 0, 1, 2, 3 and 6.

### Compare inline Yul loops and functions

`runtime-assembly-loops` renders a whole `runtime-call-graph-loops` plan as one `assembly` block:
the helpers become Yul functions and the loop a Yul `for` loop. It reaches the Yul front end's own
lowering of loop-carried variables, `break`, `continue`, `leave`, function scopes and multiple
return values. The Core reference is the call-graph loop plan of the same seed, unchanged.

A plan (`solcore-lean.assembly-loop-plan.v1`) adds a `form`, with `sc_limit := and(x, M)`:
- `for`: `for { let sc_i := 0 } lt(sc_i, sc_limit) { sc_i := add(sc_i, 1) }`;
- `break`: condition `1`, left by `if iszero(lt(sc_i, sc_limit)) { break }`;
- `continue`: condition `lt(sc_i, sc_bound())`, skipping the step once the limit is reached;
- `leave`: the `break` loop inside a Yul function, left by `leave`, with helpers that also return
  through `leave`;
- `pair`: helpers return their result and argument, bound with `let a, b := ...`.

- Generation, inputs and exclusions are `runtime-call-graph-loops'`. No emitter proof covers
  `SynthesizedAssemblyLoops.run(uint256)`.
- Fixed corpus: the first plan of each of the fifteen shapes from seed 1, 90 cases. It skips steps
  that shift by a count that may fold to a constant of at least 2^64, since such counts crash
  Sonatina code-image export on O0 and, once folded, on O2; random campaigns still generate them.
- Known finding: such random plans crash code-image export with `Integer overflow when casting to
  usize` on every backend; a reduction kept a literal shift count of 2^255.

### Compare inline Yul memory

`runtime-assembly-memory` computes the seed's primitive step through memory in one `assembly`
block, reaching the Yul front end's own byte placement for `mload`, `mstore`, `mstore8` and
`keccak256`. The step becomes the Yul function `sc_step`.

- The block reads `sc_base := mload(64)` once, never moves the free-memory pointer, and first
  writes `x`, `sc_step(x)` and `not(x)` at offsets 0, 32 and 64. A schedule from the seed runs one
  to three stages, each reading a Word and writing `sc_step` of it with `mstore` or `mstore8`,
  then a final read and optionally `keccak256` over 0, 1, 31, 32, 33 or 64 bytes.
- The Core reference keeps no memory. The window is three let-bound Words, and a read at `32k + d`
  is `(w_k << 8d) | (w_{k+1} >> 8(32 - d))`. The hash closure applies the Core Keccak-f[1600]
  permutation and digest builders of the Hull import path, proved against `KeccakSemantics`.
- Budget: 96 nodes for the step and a 3,282-node case limit. The identity filter applies. No
  emitter proof covers `SynthesizedAssemblyMemory.run(uint256)`.
- Fixed corpus: ten seeds, 80 cases, covering every stage count, access, required hazard and hash
  option. It skips plans whose step may shift by a folded constant of at least 2^64.
- Known finding: a random plan crashed O2 code-image export with `Integer overflow when casting to
  usize`; its reduction shifts by `signextend` of two literals.

### Compare generic selection

`runtime-generics` uses a polymorphic `sc_select<a>(flag, left, right)` at Word, `(word, word)` or
`sum<word, word>`. The wrapper computes `left = step(input)` and `right = step(input + 1)` before
selecting, odd input selecting left, and every selected value contributes to the result. The Core
reference contains a monomorphic curried selector closure and the applied step graph; it does not
import Rust's specialized program. The full program passes the Core checker, and the theorem
`Generic.emit_source_meaning` relates the emitted text to this reference
([scalar emitter meaning](../docs/design/scalar-emitter-meaning.md)).

- A plan (`solcore-lean.generic-plan.v1`) has the step and a `variant`: `word`, `pair` or `sum`.
  The 512-node limit includes the selector and the ABI input.
- Fixed corpus: 36 cases, requiring `word:even`, `word:odd`, `pair:even`, `pair:odd`, `sum:even`
  and `sum:odd` (`genericRequirements.instantiations`).

### Compare captured closures

`runtime-closures` captures runtime Words in source lambdas, called directly and through a
generic `sc_apply<a>`. An outer local computed with the step is captured, then incremented before
and after the second callable is chosen: `snapshot` reuses the first closure, `independent`
creates a second. The result combines both calls and the outer local.

- The Core reference loads each captured Word before building its lambda, so the body reads the
  snapshot, not the mutable cell. The pinned Rust implementation supplies the capture semantics
  under test, with no claim about the native Lean frontend.
- Scope: fixed callable identities and Word snapshots. Writes through captures, aggregate
  captures, escaped closure factories and dynamic selection between callables are separate
  scopes.
- Fixed corpus: 32 cases covering both variants.

### Compare comptime expressions

`runtime-comptime` keeps a closed G0 Word expression and an aggregate step. The source renders the
expression inside `sc_constant`, which returns `comptime<word>`, and passes it through
`sc_static(comptime value: word)`. The emitter never evaluates it or uses a Rust-computed result.

- The Core reference evaluates the expression once to `k` and calls the step once: `offset`
  returns `step(input + k) + k`, and `scale` returns `step(input) * (k | 1) + k`.
- Generation reserves at most eight nodes for the constant and needs an operation in it; random
  campaigns default to 512 attempts. Constants render only the scalar operations.
- `requiredConstantFeatures` tracks the constant apart from the step.
- Passing a runtime value to a comptime parameter is out of scope; Rust rejects it with `SC0409`.
  The comptime emitter is tested, not formally proved. The profile neither unifies the native
  Lean frontend's own staging evaluator nor claims unrestricted cross-stage persistence.
- Fixed corpus: 40 cases with both variants.
- Known finding: the recorded plan of seed `13439332813997308049` crashes O2 code-image export on
  all eight of its inputs, under revisions three and four.

### Compare module bundles and mixed features

`runtime-modules` emits four flat files with explicit imports and exports, and every provider
contributes to the result.

| File | Role |
| --- | --- |
| `case.sol` | ABI entry, staged constant, ordered provider calls and generic selection |
| `common.sol` | Closed constant expression, comptime parameter and return, generic apply and select |
| `left.sol` | Aggregate step, a Word snapshot closure and a mutation of its outer local |
| `right.sol` | A second Word snapshot closure, an input-dependent capture and an outer mutation |

- With constant `k` and input `x`, the providers capture `step(x + k)` and `x ^ k`, change their
  outer locals and pass a closure through the imported generic apply. The imported selector
  chooses left for odd input; the result is the selection plus left plus three times right plus
  `k`.
- The Core reference keeps both ASTs and builds real snapshot lambdas. It does not parse the files
  or reuse Rust's specialized constants, closures or function IDs. The module emitter's meaning
  preservation remains unproved.
- A case (`solcore-lean.semantic-module-case.v1`) carries `sourceBundle`, the four files in fixed
  order. Hull's span-derived source inventory may omit a provider, so the adapter hashes all four
  files before and after both exports; `sourceBundleReceipt` lets a moved archive replay.
- Scope: this fixed four-file graph with Word captures and results; not arbitrary or cyclic module
  graphs, dynamic ABI or equivalence with the native Lean frontend. M6 is complete for its bounded
  generic, closure, comptime and module profiles; these results prove neither source-emitter
  preservation nor language-wide compiler correctness.
- Fixed corpus: 44 cases, requiring both selection branches.
  `scripts/test-semantic-source-bundle.py` tests the bundle rules.

### Plan-based profiles

From `runtime-enums` on, each pure profile draws a plan from SplitMix64 streams of the case seed,
and its Core reference is built from the plan alone, never from the source. Shared rules:

- Saved cases hold the plan, the whole Core reference and the plan's shapes, which replay
  recomputes. The profiles record no G0 step features.
- Inputs are the primitive profile's eight boundary inputs.
- The node budget bounds the applied reference, and steps, views or uses are dropped from the end
  while it is exceeded.
- Exclusions: a plan still over the budget or not admitted, then a plan with the same outcome at
  all eight boundary inputs, or one that exhausts fuel. Reductions are strictly smaller in plan
  size, then input.
- Each fixed corpus takes, from seed 1 upwards at the default budget, every accepted plan that
  covers a missing required value, until nothing is missing. Its validator rebuilds that
  selection, recomputes every shape in Python, re-emits the source exactly, evaluates each case
  with its own model, and checks replay, reductions and tampering natively.

### Compare user-defined enums and match

`runtime-enums` targets user-defined enums and `match`, where the pinned fixtures place recent
defects: substitution in a specialized trait impl's match, pattern binding order, the scopes of
folded matches and repeated pattern bindings. A front-end defect shared by every backend is
visible only to original Core.

- One to three enums, plain or generic in `a`, have two to four constructors of zero to two
  fields: a Word, `a`, a pair or an earlier enum. Constructors are written qualified, in the dot
  form or as the same-name constructor 0, since the compiler rejects other unqualified ones
  (`SC0106`).
- One to three views (`single`, `pair` or `generic`) match random rows of constructor, tuple,
  variable and wildcard patterns, nested up to three levels, each kept only if useful. Names
  repeat and shadow freely. `run(uint256)` returns `r_0 + 3 r_1 + 5 r_2 + …`.
- The Core reference has no data definitions: an enum is the right-nested sum of its payloads, and
  each match is compiled arm by arm with the remaining arms as a failure thunk. Admission checks
  usefulness and exhaustiveness by the pattern-matrix algorithm, without the compiler.
- A Lean test compares the reference with an interpreter of first-match semantics on more than 200
  plans and a fixture against a separate Python model.
- Budget: default 2,048, minimum 256, at most 4,096 nodes.
- Fixed corpus: seven seeds, 56 cases, covering constructors, fields, declarations, views, pattern
  forms, wildcard positions and depths 1 to 3.

### Compare traits and constrained generic impls

`runtime-traits` calls one trait at instances built from Words, tuples, std sums and user enums.
It targets the defect of the pinned fixture `specialise-sum-of-product`: a binary method of
`impl<f, g> T<sum<f, g>>`, specialized at `sum<(word, word), word>`, leaked a substitution from one
match alternative into the other's nested match.

- A plan declares enums as `runtime-enums` does, `trait Sc_Fold<a>` with the unary `sc_fold` and
  the binary `sc_both`, and constrained impls at Words, pairs, sums and each enum. The sum impl's
  `sc_both` matches its second argument again inside both arms, the fixture's shape.
- One to six uses call a method at a closed type of depth 0 to 3, directly or through the helpers
  `sc_once`, `sc_twice`, `sc_lift` and `sc_lift2`.
- The Core reference lowers a std sum as a plain declaration and compiles every impl's match with
  `EnumMatch`, one closure per instance type and method the uses reach. A Lean test compares it
  with an interpreter that dispatches by instance type.
- Budget as for `runtime-enums`. Fixed corpus: five seeds, 40 cases.
- Status: the fixed corpus matched on O0 and O2. On Yul, solc rejects seed 2's eight cases with a
  `StackTooDeepError`; the matched cases still cover every shape value and input.
- Known finding: solc rejects some specialized `sc_both` methods with `StackTooDeepError`, at
  `Sc_T0<word>` with a two-column match and at `Sc_T0<Sc_T0<(word, word)>>` with a nested one. It
  occurs in sum and declaration impls under both match forms, so the fixed corpus does not avoid
  it. Recorded locally, not investigated.

### Compare trait hierarchies and method-level generics

`runtime-trait-hierarchies` adds a subclass of the `runtime-traits` trait and a chain above it.
The pinned fixtures `superclass-dictionaries`, `trait-method-generics` and
`comptime-trait-arguments` were upstream regression fixtures for these features.

- The subclass `trait Sc_Sub<a> where a: Sc_Fold` is a marker, or has the method-level generic
  `sc_mix<u>(sc_x: a, sc_y: u)`, or names that method `sc_fold` like the superclass's. The chain is
  the marker `trait Sc_Top<a> where a: Sc_Sub {}`.
- Uses call a base method directly, through helpers bounded by `Sc_Sub` or by `Sc_Top` (two bounds
  above the method's trait), through the method value `Sc_Fold.sc_fold` or through a generic
  function value; `sc_mix` is called at two argument types.
- The Core reference adds a closure per receiver and argument type of `sc_mix` to the
  `runtime-traits` closures. A superclass call through a subclass bound is the superclass
  instance's closure.
- Budget as for `runtime-enums`. Fixed corpus: thirteen seeds, 104 cases. It skips plans with a
  base-method `top` use at a tuple, std sum or generic declaration.
- Status: the fixed corpus matched on O0 and O2. On Yul, solc rejects seed 9's eight cases with a
  `StackTooDeepError`.
- Known findings, recorded locally, not investigated; no mismatch was found:
  - The checked frontend rejects a base method reached through two superclass steps at a tuple, a
    std sum or a generic declaration with `SC0406` "no unique dictionary". Plans keep generating
    such uses, so random campaigns report them as `source-rejected` and reduce them.
  - solc's `StackTooDeepError` on Yul, as for `runtime-traits`.

### Compare Solcore memory values

`runtime-memory-values` generates std's `memory<bytes>`, `memory_ref` and
`memory<DynArray<uint256>>` values in straight-line code and in the bounded `while` forms. The
pinned fixtures `concat`, `slices`, `zeroize-memory-range`, `loop-value-copies`,
`abi-byte-memory` and `abi-codec-memory` use these values directly.

- `run(uint256)` runs one to ten steps: bytes values from `to_bytes` or `concat`, slices from
  `slice_` and `truncate`, aliases and arrays; Word and byte writes inline or through helpers;
  observations of lengths, Words, bytes, `keccak256_` hashes and elements; at most one loop.
  Indices can fall out of range.
- The Core reference models every value as its byte list, a length and at most four Words. A slice
  is a start and a length over its value, so writes are seen through every alias and slice and
  never through a copy.
- An out-of-range access fails with std's revert data: `OutOfBounds()` (`0xb4120f14`) for a
  value's Words and bytes, and `Panic(0x32)` for an array element since solcore-rs `e2eef194`.
  Three paths that reverted with the same data match.
- Budget: default 1,024, minimum 256, at most 2,048 nodes, without the 2,723-node hash closure.
- Fixed corpus: 29 seeds, 232 cases, covering values, parts, cuts, writes, observations, indices,
  hazards, loops and hashed lengths. It skips plans whose loop writes a bytes value or slice.
- Known finding: before `e2eef194`, Sonatina O0 returned other Words than Core and Hull for some
  loops over bytes values and slices, in four fixed cases and in random campaigns. The class no
  longer occurs at `e2eef194`, where the fixed corpus matched on every backend; the fuzz driver
  keeps it registered ([continuous fuzzing](SEMANTIC_CI.md#continuous-fuzzing)).

### Compare Solcore memory calls

`runtime-memory-calls` passes memory values to one to three helpers, which read them, write
through and return them, return a slice or a fresh copy, pack them into a pair, take them out of a
pair, sum or enum, or call an earlier helper. Generic helpers run at bytes values and slices,
function values call helpers, and closures capture values. Plans stay straight-line, since
`runtime-memory-values` covers loops.

- The Core reference is the memory value model with every call inlined, so a helper's write is
  seen through every variable, slice, data value and closure that holds the value. Out-of-range
  accesses revert with `OutOfBounds()` or `Panic(0x32)`, compared exactly.
- Budget as for `runtime-memory-values`.
- Fixed corpus: 41 seeds, 328 cases, 47 of them out of range, covering every helper kind, pass,
  instance, closure and hazard.
- Decision: compact case files, since indented ones stopped the fixed corpus at the disk limit.

### Compare Solcore revert data

`runtime-revert-data` computes std `Error` values as data and reverts with them on
input-dependent paths: `Error(W)` with a selector Word from the input, `Error.Empty`, `Error.Msg`
over a bytes value, `require(C, E)`, `require(C, "…")`, `revertLit("…")` and `revertEmpty()`, in
`run`, helpers, closures, match arms and a bounded loop. `assert`'s `invalid()` is left out, since
it reverts without data.

- The Core reference returns the fold or the revert data, at most 64 bytes. The first site whose
  condition holds raises, and a message's data are its value's bytes at the site. The adapter
  compares revert data exactly.
- `revertLit` takes the texts of at most 32 bytes, which Sonatina requires.
- A loop body builds bytes values and raises but never reads or writes one, avoiding Sonatina O0's
  recorded loop mismatches.
- Budget: default 1,024, minimum 256, at most 2,048, case limit 4,096 nodes.
- Fixed corpus: 19 seeds, 152 cases, 87 of them reverting with 0 to 64 bytes of data.

### Compare Solcore halts

`runtime-halts` keeps the revert data plans and lets any site halt instead: std's `assert(C)`,
`std.opcodes`' `invalid()`, `assembly { invalid() }` under a Solcore `if`, or a Yul `if` with the
same test. An optimizer that treated `invalid()` as unreachable could drop the condition or the
halt, which only a compared halt shows.

- The Core reference raises a revert length of `2^256 − 1`, which no revert data has.
- Original Core and the Lean Hull runner report `invalid`, and Anvil `EVM error InvalidFEOpcode`.
  The adapter classifies revm's halt names: `InvalidFEOpcode` is `invalid`, `OutOfGas` and names
  ending in `OOG` are `out-of-gas`, the rest `evm-exceptional`.
- Three `invalid` observations match. A halt on one or two paths is a semantic mismatch, and
  exhausted gas or fuel on any path is inconclusive.
- Exclusions drop a plan that halts at no boundary input, so no identity filter is needed.
- Fixed corpus: 12 seeds, 96 cases, 31 of them halts and 19 reverts.

### Compare Solcore integer arithmetic and shifts

Two profiles reach upstream's integer operators: checked `+ - * / %` over `uint8` … `uint256` and
`int8` … `int256`, which revert with `Panic(0x11)` or `Panic(0x12)`, the wrapping `unchecked { … }`
blocks, and `<<` and `>>` with an unsigned amount. They share `Solcore.Synthesis.Internal.Integers`.

- `runtime-checked-arithmetic` converts the input to one integer type, with up to two more inputs
  offset to the type's extremes. It runs one to ten operations, compound assignments, helper calls
  and lambda applications, in checked code and up to three `unchecked` blocks. A quarter of the
  plans take `run(T)`, so std's decoder rejects dirty high bits with `DirtyHigherBitsForInteger()`
  (`0x6cc54a63`), and a quarter return a narrow `T`.
- `runtime-shifts` shifts a Word or an integer by one to three runtime amounts, or by literal
  amounts up to 300, inline or as `<<=` and `>>=`.
- The Core reference computes exactly with Core integers: a zero divisor raises `Panic(0x12)`,
  quotients round toward zero, a checked result outside its type raises `Panic(0x11)`, and an
  unchecked one wraps. `<<` gives 0 for an amount of at least the width, `>>` the floor quotient,
  and an amount of at least 256 gives 0 or `-1`.
- Budget: default 1,024, minimum 256, at most 2,048, case limit 4,096.
- Fixed corpora: checked arithmetic 136 cases and shifts 128. Checked arithmetic requires every
  value but the per-type outcomes, which would take 37 seeds.

### Compare Solcore memory arrays and their ABI

Since solcore-rs `e2eef194` (#145), `T[]` is a memory array, `new T[](n)` allocates `n` zeroed
elements, `a[i]` reads and writes through a checked `memref`, slices are read-only views, a field
`T[]` is a storage array with `push`, `pop` and `setLength`, and memory arrays appear in the
public ABI. An index or bound out of range reverts with `Panic(0x32)`, an empty `pop` with
`Panic(0x31)` and an oversized allocation with `Panic(0x41)`. Two profiles share
`Solcore.Synthesis.Internal.Arrays`:

- `runtime-memory-arrays` runs one to twelve steps over one of twelve integer types: arrays,
  slices in all four forms, `T[][]` grids, plain, compound and `memref` writes, the storage array's
  members, observations and at most one loop.
- `runtime-array-abi` takes one or two `T[]` or `calldata<T[]>` parameters, with raw narrow
  elements half the time, so std's decoder rejects some, and returns the fold or a `T[]`.
- The Core reference holds an array as a length cell and eight element cells, so aliases, grid
  rows and memory parameters share writes and a copy is new. Every index, bound, allocation and
  `pop` is checked as std checks it. The adapter encodes the ABI profile's calldata itself.
- Budget: default 1,024, at most 2,048, at least 256, or 512 for the ABI profile.
- Fixed corpora: memory arrays 288 cases and the array ABI 144, covering every outcome and panic.
- Decision: the emitter avoids two frontend rejections, a converted literal as a `new` length and
  `Typedef.rep(s[0])` with a literal index of a let-bound slice or calldata parameter.
- Caveat: on Yul, `runtime-memory-arrays` used 619 of the 900 seconds CI allows a profile.

### Compare Solcore closures by value and closure factories

solcore-rs #120 decided that a closure captures by value: it keeps its captured locals' values
from creation, a write in its body reaches only that call's copy, and each call starts again from
the creation-time values. Since `bf7114a8` and `ad1f49cf`, a closure factory resolves its captures
in its own scope. Two profiles share `Solcore.Synthesis.Internal.Captures`:

- `runtime-closure-captures`: closures from lambdas and aliases, writes to captured locals,
  parameters and the field `sc_n`, rebinding, calls directly, through `sc_apply` and `sc_twice`
  and in a loop, and checked `uint256` `+` and `/`;
- `runtime-closure-factories`: one or two factories `sc_mk<k>(sc_p: word)`, free functions or
  methods, that return closures, one of which may call the other.

- The pin lowers only closures that are statically one lambda and rejects the rest with `SC0422`,
  so admission keeps plans to the lowered forms.
- Every local is assigned where it is declared: Lean faults on reading an unassigned local, while
  the pin reads it as zero.
- The Core reference holds every local in a cell. A closure snapshots its captures, and each call
  copies them into fresh cells, so body writes stay in that call. Overflow and division by zero
  raise `Panic(0x11)` and `Panic(0x12)`, compared exactly.
- Budget: default 1,024, minimum 256, at most 2,048.
- Fixed corpora: closure captures 80 cases and closure factories 112.

## Stateful profiles

### Stateful conventions

Rules shared by the stateful profiles, unless a section says otherwise:

- **Step.** Each contract applies a checked aggregate step, generated as for the aggregate
  profiles. Random campaigns draw it with [G0 revision three](#revision-three-swarm-masks),
  passing `core-g0-v3/lcg64-v1` after `FUEL` to `generate`, and every helper uses the scenario
  seed's swarm mask (`provenance.swarmMask`). `--g0-version` selects v1 or v2. A fixed corpus or
  a saved case keeps its recorded version, and a reduction keeps its parent's version and mask.
- **Transactions.** Generated scenarios have three transactions; random campaigns request
  `--transactions` (one to eight, default eight), passed after the version. A sequence is the
  first transactions of consecutive three-transaction blocks, and block zero is the seed's
  original three, so three transactions regenerate the fixed corpora bit for bit. Imported
  scenarios have one to three. A generated origin records another count as `transactionCount`.
- **Streams.** Since the `...-sequence-seed-v2` versions, every stream of a stateful case module
  starts at SplitMix64's finalizer of the block or scenario seed xor its domain. Reason: raw
  streams made consecutive seeds' first-block choices lose values or step by a fixed residue.
- **Protocol.** Most contracts take `flags` and, when the flags are odd, revert after their writes
  with the result Word as a 32-byte payload; otherwise they return it. Generation draws one of
  four completion patterns (all return, or one revert in the first, second or third position),
  and original Core must complete with exactly those outcomes.
- **Observations.** Declared-slot profiles declare `observedSlots`, and all three paths report
  status, payload and every declared slot after every transaction. The Hull and EVM paths must
  hold no nonzero slot outside the declaration (`undeclaredStorage`): the Hull runner reports
  every nonzero committed slot, and the EVM path asks Anvil's `prestateTracer` in diff mode. Every
  profile also compares the [whole committed storage](#compare-whole-committed-storage).
- **Rollback and deployment.** A revert keeps the prior committed slots on every path, chosen by
  `ContractRuntime` for original Core. An incomplete transaction ends the sequence. Unless noted,
  the constructor is empty with zero value, every declared slot starts at zero, and original Core
  starts from the declared post-deployment world.
- **Reduction.** Candidates first remove one transaction, last first, then simplify the step,
  keeping every helper and binder, then the profile's inputs. The fingerprint names a stable
  transaction ID, the differing fields and slots, the disagreeing paths and the outcome forms. A
  candidate rederives its declared slots, so one that drops a finding's slot cannot keep it.
- **Shrink batches.** A shrink request asks for at most `--shrink-candidates`, or the profile's
  `shrinkBatch` (8, 16 or 32 for profiles with large cases), never more than the attempts left;
  `--shrink-batch` replaces the first batch. A response over `min(4 MiB, --disk-bytes / 64)`
  halves the batch, down to one candidate (`halvedBatches`); only a one-candidate response over
  the bound stops the reduction.
- **Fixed corpora.** Most mix imported plans that reuse earlier corpus steps with generated seeds.
  Expected histories were computed outside Lean by an independent evaluator and a direct model
  of the protocol, and since the mixed sequence seeds by a direct Lean model with the step run
  alone in Core. A registered Lean validator compares every entry with original Core and rejects
  tampered entries. Coverage includes the step AST features, the boundary inputs, one to three
  helpers and transactions, the four step templates, both outcomes and the completion patterns.
- **Scope.** No profile compares gas, nonces or code. Agreement is test evidence, not a
  preservation proof.
- **Backends.** Every storage-family profile and the three return-data call profiles also run on
  [Yul](#compare-storage-family-contracts-on-yul). Unless a section names a finding, the fixed
  corpus matched on every backend the profile runs on.

Build a profile's case tool and Hull runner with its line:

```sh
lake build semanticStorageTool rustHullStorageScenario               # stateful-storage
lake build semanticStorageRollbackTool rustHullStorageScenario       # stateful-storage-rollback
lake build semanticCallTool rustHullCallScenario                     # stateful-calls
lake build semanticKeyedStorageTool rustHullKeyedStorageScenario     # stateful-keyed-storage
lake build semanticDynamicArrayTool rustHullKeyedStorageScenario     # stateful-dynamic-array
lake build semanticEventLogTool rustHullKeyedStorageScenario         # stateful-logs
lake build semanticCallValueTool rustHullValueScenario               # stateful-call-value
lake build semanticBytesTool rustHullKeyedStorageScenario            # stateful-bytes
lake build semanticForwardTool rustHullForwardScenario               # stateful-forwarded-value
lake build semanticMappingTool rustHullKeyedStorageScenario          # stateful-mapping
lake build semanticLedgerTool rustHullLedgerScenario                 # stateful-ledger
lake build semanticLongBytesTool rustHullKeyedStorageScenario        # stateful-long-bytes
lake build semanticNestedArrayTool rustHullKeyedStorageScenario      # stateful-nested-array
lake build semanticMalformedCalldataTool rustHullKeyedStorageScenario
lake build semanticMalformedNestedArrayTool rustHullKeyedStorageScenario
lake build semanticMalformedBytesTool rustHullKeyedStorageScenario
lake build semanticMethodsTool rustHullKeyedStorageScenario          # stateful-methods
lake build semanticStorageLoopTool rustHullKeyedStorageScenario      # stateful-storage-loops
lake build semanticKeccakLoopTool rustHullKeyedStorageScenario       # stateful-keccak-loops
lake build semanticAssemblyStorageLoopTool semanticAssemblyKeccakLoopTool \
  rustHullKeyedStorageScenario                                       # the inline Yul loops
lake build semanticAdtStorageTool rustHullKeyedStorageScenario       # stateful-adt-storage
lake build semanticTupleReturnTool rustHullKeyedStorageScenario      # stateful-tuple-returns
lake build semanticBytesReturnTool rustHullKeyedStorageScenario      # stateful-bytes-returns
lake build semanticEnumReturnTool rustHullKeyedStorageScenario       # stateful-enum-returns
lake build semanticEnumArgumentTool rustHullKeyedStorageScenario     # stateful-enum-arguments
lake build semanticEnumArrayTool rustHullKeyedStorageScenario   # stateful-enum-array-arguments
lake build semanticArrayReturnTool rustHullKeyedStorageScenario      # stateful-array-returns
lake build semanticConstructorArgumentTool rustHullKeyedStorageScenario
lake build semanticCallReturnTool rustHullCallReturnScenario         # stateful-call-returns
lake build semanticCallSequenceTool rustHullCallReturnScenario       # stateful-call-sequences
lake build semanticCallBranchTool rustHullCallReturnScenario         # stateful-call-branches
```

Then run its corpus with `semantic-storage-campaign.py --corpus scripts/<stem>-corpus.json`, or
`semantic-call-campaign.py --profile P --corpus ...` for a call profile, and a random suite with
`semantic-suite.py --mode random --profile P --cases 16`.

### Compare ordered storage transactions

`stateful-storage` runs `SynthesizedStorage.run(uint256)` (selector `0xa444f5e9`). It reads slots
0 and 1, applies the step to `input + old0`, writes the result to slot 0, increments slot 1 and
returns the sum of both reread slots. Transactions are `{id, input, calldata, value}` with value
`"0"`.

- Scope: valid `run(uint256)` inputs, zero call value, initially empty slots 0 and 1 and
  successful Word returns. It does not establish equivalence of arbitrary storage, gas,
  balances, nonce, logs or account lifecycle.
- Fixed corpus `scripts/semantic-storage-corpus.json`: 12 scenarios.
- `python3 scripts/test-source-storage-rust.py` covers feedback, repeated inputs, sparse zero
  storage, clearing and rewriting a slot and fresh private cells, with exact replay.

### Compare rollback after storage writes

`stateful-storage-rollback` keeps the two-slot protocol in `SynthesizedRollback.run(uint256)`.
Both writes and the final reads run before the input selects completion: an odd input reverts
with the tentative slot sum as exactly 32 bytes, an even input returns it.

- The Core contract uses `wordOutcomeV1`. `ContractRuntime` selects the committed or the
  rolled-back world; the wrapper restores nothing itself. The source emits `mstore(0, result)`
  and `revert_(0, 32)`.
- The comparison also checks that each reverted snapshot equals its predecessor. A reducer cannot
  keep a reverted-payload finding by turning it into a return, an empty payload or a resource
  failure.
- Generated scenarios run even, odd, even and must return, revert and return.
- Fixed corpus: 14 scenarios; `requiredCompletionPatterns` covers four completion patterns.

### Compare bounded parent/child calls

`stateful-calls` installs `SynthesizedCaller` and `SynthesizedCallee`. The parent's payable
constructor receives eight units, the child's none. Original Core starts from the declared
post-deployment world; Rust EVM and imported Hull run the real deployments, whose initial
accounts the runner checks.

- Each zero-value transaction calls `SynthesizedCaller.run(uint256 target, uint256 input)`
  (`0x7357f5d2`). The parent calls the payable child fallback with one raw Word and rejects child
  return data that is not exactly 32 bytes.
- The low three input bits choose: `1` the child reverts after its writes and log, `2` the parent
  reverts after writing and logging its result, `4` the parent sends one unit to the child.
- The parent adds the input to slot 0 and logs topic one. The child applies the step to
  `input + oldChild0`, writes slots 0 and 1 and logs topic two. The parent writes the child's
  payload to slot 1, plus one if the child reverted, and logs topic three.
- Original Core runs through `OneLevelNestedExecution.run`. Every prefix compares the root status
  and payload, both accounts' slots and balances, both contracts' whole storage and the ordered
  logs. A root rollback restores both accounts and drops the logs; a child rollback can leave
  earlier parent effects.
- Bindings come from `solcore-lean.call-bindings.v1`; contract addresses 0 to 17 and 256 are
  excluded at the Osaka boundary.
- Fixed corpus `scripts/semantic-call-corpus.json`: 16 scenarios. Coverage separates the
  prescribed `input & 7` modes from the observed outcomes and log patterns.
- Scope: one parent and one child with valid Word calldata. Gas and nonce equivalence,
  precompiles, arbitrary accounts and deeper calls are out. M5 is complete within its documented
  profiles.

### Compare keyed storage transactions

`stateful-keyed-storage` calls `SynthesizedKeyedStorage.run(uint256 key, uint256 input)`
(`0x7357f5d2`). It reads `old = sload(key)` and `count = sload(0)`, then writes in order the step
of `input + old` to `key`, `old` to `key + 1` (wrapping) and `count + 1` to slot 0, and returns
the wrapped sum of the three reread slots.

- Later writes win when slots alias: key zero is the counter, and the maximum key's successor
  wraps to it. `observedSlots` is the counter and every key and successor.
- Keys come from a bank of zero, one, the high bit, a full-width pattern, maximum minus one and
  maximum.
- Fixed corpus: 14 scenarios, requiring the six keys and the static alias kinds `key-counter`,
  `successor-counter`, `repeated-key` and `successor-key`. These describe the keys, not a
  committed aliasing write.
- Scope: no malformed calldata, Solidity-style hashed layouts, dynamic ABI values, multiple
  callers or call value.

### Compare bounded dynamic arrays

`stateful-dynamic-array` calls `SynthesizedDynamicArray.run(uint256 flags, uint256[] values)`
(`0x9a94c44b`) with zero to three elements in the canonical head and tail encoding. The source
reads a lazily decoded `calldata<array<uint256>>`; original Core follows the head offset to the
same Words with `inputDataWordBE?`.

- Each present element `i` gives `acc = step(acc + values[i])`, written to slot `1 + i`. The
  accumulator goes to slot 0 and the length to a count in slot 4; the result is slots 0 plus 4.
- The tool and the adapter reject non-canonical calldata and arrays over three elements;
  calldata matched `cast calldata` byte for byte.
- Scope: non-canonical offsets, truncated arrays and the decoder's revert paths are out, since Core
  reads an absent Word as zero while the decoder reverts.
- Fixed corpus: 15 scenarios, requiring lengths 0 to 3.
- Known finding: a random scenario crashed O2 code-image export with `Integer overflow when
  casting to usize` (Q013); it matched on O0, and its reduction still shifts by a large constant.

### Compare committed event logs

`stateful-logs` calls `SynthesizedLogs.run(uint256 flags, uint256 input)` (`0x7357f5d2`). A plan
holds the step and zero to three log sites, each with a guard bit `g` of 1, 2 or 3, a topic count
`n` of 0 to 4 and zero to two data Words.

- The contract writes `result = step(input + old)` and a count. Each site whose guard bit is set
  emits one LOGn with `value = step(result + g)`: topics `value + 1` to `value + n`, data `value`
  then `result`. The source uses `std.opcodes`' `log0` to `log4`.
- Original Core's host has one log primitive, `emitLogWord`, with one topic and one data Word.
  The Core contract writes each site as a frame of `1 + w + n` word logs under
  `core-word-log-framing-v1` (a header with topic `256 + 16 * w + n`, data records `512 + i`,
  topic records `768 + j`). An incomplete frame is an observer failure. The framing is this
  profile's convention, not a Core LOGn semantics.
- A reverted transaction commits no logs, and `eth_getLogs` over the whole chain must equal the
  receipt logs. Each path's logs must have the shape the plan and flags fix.
- Fixed corpus: 12 scenarios that commit 29 logs, requiring every log count, topic arity and data
  length.
- Known finding: a random scenario crashed O2 code-image export with the host panic `arithmetic
  operation overflow` in `primitive-types`, from Sonatina's signextend folding; it matched on O0.
- Scope: no constructor logs, logs from several contracts or ABI event signatures.

### Compare nonzero call value

`stateful-call-value` sends value to the payable
`SynthesizedCallValue.run(uint256 flags, uint256 input)` (`0x7357f5d2`), from the bank 0, 1, 7,
2^64 − 1, 2^64 and 2^70.

- The contract writes `step(input + value + old)` to slot 0 and adds the value to slot 1, so every
  committed balance must equal the deployment value, 0 or 5, plus slot 1.
- All paths report the contract's committed balance; the sender's is never observed, since on the
  EVM it also pays gas.
- Original Core runs `BalancedTopLevelExecution`, which moves the value before the root runs. The
  Hull runner `rust-hull-value-scenario` does the same in its checked ledger and reports a
  rejected transfer as `transfer-rejected`, an execution error. A revert refunds the value.
- Fixed corpus: 12 scenarios, requiring every bank value, refunds and both deployment values.
- Scope: no value sent by contracts and no non-payable methods, whose 4-byte rejection the Word
  convention cannot express.

### Compare bounded dynamic bytes

`stateful-bytes` calls `SynthesizedBytes.run(uint256 flags, bytes payload)` (`0x220eb9b6`) with
0 to 64 bytes. The pinned dialect decodes `bytes` only into memory, so the parameter is
`payload: memory<bytes>`, copied with `calldatacopy` and zero-padded.

- Each present 32-byte chunk gives `acc = step(acc + chunk)`, written to slot `1 + k`. The length
  goes to slot 3 and the last byte to slot 4, and the result is
  `sload(0) + sload(3) + sload(4) + calldatasize()`.
- Original Core reads calldata directly, chunks masked to the length. The source reads the decoded
  copy, the last byte as an unaligned `mload(data + length) & 255`.
- Lengths come from the bank 0, 1, 17, 31, 32, 33, 48, 63 and 64.
- Fixed corpus: 12 scenarios, requiring every bank length.
- Scope: truncated input is out, since the Rust decoder rejects it with a 4-byte error the Word
  convention cannot express, while Core reads an absent byte as zero.

### Compare `bytes` payloads beyond 64 bytes

`stateful-long-bytes` extends the bytes profile to 256 bytes in
`SynthesizedLongBytes.run(uint256 flags, bytes payload)`. It was built as the fallback for
multi-word returns, before Core had an entry convention for them.

- Chunks 0 to 7 fold into slots 1 to 8; the count goes to slot 9 and the last byte to slot 10.
- The eight chunk guards lie outside the step's node budget, so a contract may exceed the
  requested budget by their size.
- Lengths come from the bank 0, 1, 64, 65, 96, 97, 128, 129, 192, 223, 255 and 256.
- Fixed corpus: 12 scenarios, requiring every bank length.

### Compare nested dynamic arrays

`stateful-nested-array` calls `SynthesizedNestedArray.run(uint256 flags, uint256[][] values)`
(`0x7095aff8`) with at most three rows of at most two elements, read through a lazily decoded
`calldata<array<calldata<array<uint256>>>>`.

- Each present element folds into slot `1 + 2i + j`; the row count goes to slot 7 and the element
  count to slot 8.
- Original Core reads the head offset, the outer length, each row's offset and each row's length
  with `inputDataWordBE?`; the source's lazy view checks each index against its length.
- Fixed corpus: 12 scenarios, requiring outer lengths 0 to 3 and row lengths 0 to 2.

### Compare Keccak-addressed storage mappings

`stateful-mapping` stores through `entries: mapping(word => word)` at base slot 1 beside a counter
at slot 0. `SynthesizedMapping.run(uint256 flags, uint256 key, uint256 input)` (`0x24b912e5`)
writes `entries[key] = step(input + old)` and `entries[key + 1] = old + 1`, increments the counter
and returns the sum of the three.

- The pinned std indexes a mapping with `hash2(p, k)`, so an entry lives at `keccak256(p ++ k)`:
  the reverse of Solidity's `keccak256(k ++ p)`, although the std comment cites Solidity's layout.
  The profile follows the pinned dialect.
- Original Core derives the slots itself with the Core Keccak-f[1600] permutation and digest
  builders of the Hull import path, proved against `KeccakSemantics` (`permute_evaluates`,
  `digest_evaluates`). The EVM computes Keccak independently, and the corpus's slots come from
  `cast keccak`. The 2,654-node closure lies outside the step's budget.
- Keys come from a bank with successor pairs and the maximum. Coverage adds a repeated key, a key
  that is another's successor and the maximum key, whose successor wraps to zero.
- Fixed corpus: 12 scenarios; the validator rejects a slot in Solidity's order.
- Scope: other key or value types, other base slots and nested mappings are out.

### Compare a sender-keyed mapping ledger

`stateful-ledger` keys the mapping's entries by the sender.
`SynthesizedLedger.run(uint256 flags, uint256 recipient, uint256 amount, uint256 input)`
(`0x15509d2b`) is called from Anvil's first three default accounts; the first deploys.

- The contract credits `B = entries[sender] + step(input)`. If `amount > B` it reverts with `B`
  without writing; otherwise it moves `amount` to the recipient and increments the counter.
- Original Core runs `TopLevelExecution` with that caller. The Hull runner
  `rust-hull-ledger-scenario` takes a declared sender set, and the EVM path sends from each
  sender's unlocked account.
- The adapter checks the ledger protocol from each row and the prior slots: an even-flag revert
  must report a balance below the amount, and a returned row changes only the counter and two
  entries. Three paths agreeing on a row that breaks it is still a mismatch.
- Recipients are the senders, 0, 2^160 − 1 and 2^256 − 1; amounts come from the call-value bank.
  Coverage adds both revert causes, self-transfers and repeated senders.
- Fixed corpus: 12 scenarios.
- Scope: balances, value-bearing transfers and contract callers are out.

### Compare malformed calldata

`stateful-malformed-calldata` sends the dynamic-array contract calldata with one malformation per
transaction and compares the paths against the pinned std's dispatcher (`std/dispatch.sol`) and
decoder (`std/std.sol`). The original Core contract `core-malformed-calldata-contract-v1` makes
std's checks on the actual calldata, in std's order:

1. Fewer than 4 bytes or another selector reverts with `0x4924aef0`
   (`NoSelectorMatchedWithoutFallback()`).
2. Fewer than 68 bytes reverts with `0x08638556` (`ABIInputTruncated()`).
3. A head offset `o > size - 4`, fewer than 32 bytes at `4 + o`, a length above `2^251 - 1` or
   `32 * length > size - (36 + o)` reverts with `0x08638556`.
4. Otherwise the protocol runs on the decoded Words; overlaps and trailing bytes are ignored.

- Malformations: `none`, `short`, `selector`, `truncate`, `trailing`, `offset` (out of range,
  wrapping or overlapping) and `length`. Calldata is at most 1 KiB.
- `stdRejection` is the rejecting selector or `null`, from a second std model over the bytes
  (`stdRejection?`); the adapter checks it with a third model of its own.
- **Selector rule.** A Core contract reverts with one Word, so the wrapper reverts with the
  selector as its Word. When it does and `stdRejection` is that selector, Rust EVM and imported
  Hull must each revert with exactly those four bytes. Every other row is compared exactly, Hull
  against EVM byte for byte, and `selectorRows` lists the rows compared by selector.
- `Tests.SourceMalformedCalldataGolden` checks the wrapper and `stdRejection?` against 35 golden
  cases from the std reading. Reason: a false agreement would need both models to reject a
  transaction std accepts while both compiled paths reject it with the same selector.
- The std checks take 273 nodes, so the suite's default budget is 448.
- Fixed corpus: 13 scenarios, requiring every malformation kind, both selectors and acceptance.
- Scope: value-bearing malformations, malformed constructor calldata and calldata over 1 KiB are
  out. Every length is checked against the calldata size before any copy.

### Compare malformed nested arrays

`stateful-malformed-nested-array` does the same for the nested-array contract, against std's lazy
decoder (`core-malformed-nested-array-contract-v1`):

1. Dispatch and the outer array are checked as above, with selector `0x7095aff8`, and the whole
   offset table must fit.
2. Each read row `i < min(n, 3)` is checked as it is decoded: its table offset, its length Word,
   a length above `2^251 - 1` and its whole element region, skipped elements included.
3. Rows past the third are never decoded. A bad row reverts after earlier rows were folded, but a
   revert commits nothing.
4. Overlaps between table entries, rows and the head are not checked.

- Malformations add `row-offset` and `row-length` for a present row. The adapter's third model is
  `nested_std_decode`.
- `Solcore/Synthesis/Core/StdDispatch.lean` and `Solcore/Synthesis/Stateful/Sequence.lean` hold
  the std checks in Core and the byte-level model shared by the three malformed profiles.
- `Tests.SourceMalformedNestedArrayGolden` checks 64 golden cases, among them overlaps std
  accepts and a malformed fourth row that is never read.
- Fixed corpus: 13 scenarios, requiring row malformations of rows 0 to 3.

### Compare malformed bytes

`stateful-malformed-bytes` does the same for the long-bytes contract, against std's `bytes`
decoder (`core-malformed-bytes-contract-v1`):

1. Dispatch and the head are checked with selector `0x220eb9b6`.
2. A payload length `L > size - (36 + o)` reverts with `0x08638556`, so std's later
   `require(length <= ~0 - 63)` can never fail.
3. std copies the payload and zeroes the padding in memory, so the calldata padding is not read:
   a cut inside it is accepted and nonzero padding is ignored.
4. When a cut leaves the last chunk incomplete, Core reads the Word that ends at the last payload
   byte, shifted to the chunk's start.

- Malformations add `padding`. The adapter's third model is `bytes_std_decode`.
- `Tests.SourceMalformedBytesGolden` checks 40 golden cases; offset 0 decodes the flags as a
  two-byte length.
- Fixed corpus: 13 scenarios, requiring all twelve payload lengths.

### Compare several methods

`stateful-methods` gives `SynthesizedMethods` two to four external methods over shared slots and
compares the paths against std's dispatcher. The compiler builds std's method tuple in
declaration order, the first matching selector runs, and a missing selector reaches the default
fallback.

- Method `i` is named `m_` and eight hex digits from the seed and takes zero to two `uint256`.
  Selectors are distinct and recorded in `ascending`, `descending` or `mixed` order.
- Slot 0 is a shared accumulator, slot 1 a call count and slot `2 + i` method `i`'s last result.
  Each method has its own step, under the case's one swarm mask.
- `core-methods-contract-v1` dispatches through `StdDispatch`: short calldata or no match reverts
  with `0x4924aef0`, a short head with `0x08638556`.
- A transaction calls a method or sends a missing selector. The adapter recomputes selectors with
  its own Keccak and the outcome with `methods_dispatch`.
- `Tests.SourceMethodsGolden` checks 110 calls written out by hand; the selectors match `cast sig`.
- Fixed corpus: 12 scenarios, requiring every method count, position and order.
- Scope: payable methods, fallbacks and overloaded names are out.

### Compare storage-writing loops

`stateful-storage-loops` runs a bounded `while` loop whose iterations read and write declared
slots, where store forwarding, loop-invariant motion and O2's memory and storage passes act.

- `SynthesizedStorageLoops.run(uint256 flags, uint256 input)`: slot 0 is an accumulator, slot 1
  the iteration total and slots 2 to 8 one per iteration.
- `limit = input & M` with `M` in {0, 1, 3, 7}. Iteration `i` reads slots 0, 1, `1 + i` and
  `2 + i`, and writes the step of their sum plus the input to slot `2 + i` and then to slot 0.
- Original Core has `M` ordinal guards with literal slots and no counter cell. A returned row
  must follow the loop protocol on every path.
- Fixed corpus: 12 scenarios, requiring every mask and iteration count, an iteration that reads
  the previous one's write and a revert that discards loop writes.

### Compare loops over Keccak-addressed entries and logs

`stateful-keccak-loops` hashes a slot and emits a log in every iteration, so Keccak, memory,
storage and log lowering meet inside one loop body.

- `SynthesizedKeccakLoops` has `acc` at slot 0 and a mapping at base slot 1. With
  `limit = input & M`, `base = input & ~7` and a key mask `S`, iteration `i` uses the key
  `base | (i & S)`, writes `step(entry + acc + input)` to the entry and to `acc`, and emits `log2`
  with that value and the topics `i` and the key.
- Iterations share an entry when `i & S` agrees; transactions share one when their inputs share
  the high part.
- Original Core uses the mapping's Keccak closure and `M` ordinal guards, with logs framed as in
  `stateful-logs`. Observed slots are derived with `Solcore.Abi.V1.Keccak256`.
- Fixed corpus: 13 scenarios committing 77 logs, requiring every mask, iteration counts 0 to 7
  and carries across iterations, entries, transactions and a rollback.

### Compare storage and Keccak loops through inline Yul

`stateful-assembly-storage-loops` and `stateful-assembly-keccak-loops` render the two loop plans
with every storage access, hash, log and completion in `assembly` blocks. Each keeps its parent's
plan, Core reference, observations and reductions, and adds a `form`.

- The loop stays in Solcore, because the pinned front end resolves a Yul call only to a builtin
  or a Yul function of the enclosing blocks.
- Forms: `split` reads before the step call and writes after it; `carried` passes the slot to the
  write block through a Solcore local; `pipelined` reads the next iteration in the same block.
- Each fixed corpus repeats its parent's scenarios across the forms: 16 scenarios for storage
  loops and 19 for Keccak loops.

### Compare enum and struct values in storage

`stateful-adt-storage` stores user `enum` and `struct` values in fields and behind mapping keys,
laid out by `std.StorageGeneric`, and reads them back with `match`.

- `enum ScChoice` has two to four variants of zero to three Word fields or one `struct ScPair`;
  `struct ScRecord { f0; f1; f2; }` holds the enum at a drawn position.
- Layout: a sum takes one tag slot and the larger of its first variant and the sum of the rest. A
  payload-free write leaves the payload slots as they were.
- `SynthesizedAdtStorage` declares the methods its transactions call, from `putChoice`,
  `putChoiceAt`, `clearChoice`, `clearChoiceAt`, `getChoice`, `getChoiceAt`, `putRecord`,
  `putRecordAt`, `setRecord`, `setRecordAt`, `getRecord` and `getRecordAt`. An entry's field
  update writes the whole record, since the front end rejects `records[k].f = v` (`SC0201`).
- Original Core (`core-adt-storage-contract-v1`) computes the layout itself, as slot arithmetic
  over the base slots and the mapping's Keccak closure, independent of std's layout code. An
  independent Python model predicts every observed slot, at most 31.
- Caveat: deploying the larger contracts from Sonatina O0 images takes up to 15,000,000 Hull fuel,
  so the suite's default `--core-fuel` is 40,000,000; with less they are `inconclusive-resource`.
- Fixed corpus: 26 scenarios, requiring every variant count, payload kind, position, Word type
  and method, every ordered pair of variants at one place, stale reads and reverted writes.

### Compare ABI-encoded tuple returns

`stateful-tuple-returns` returns a static ABI tuple of two to four Words and compares the whole
return data.

- Convention: `CoreContractEntryProfile.wordTupleOutcomeV1 extraWords` returns the right-nested
  pairs of `extraWords + 2` Words as their concatenated encodings. Revert and trap carry one Word.
- A word call carries exactly one Word, so the nested executor treats a tuple contract as
  `unavailable` to a word call, and a tuple initializer to creation. One-Word theorems take
  `returnsOneWord` as a premise.
- `SynthesizedTupleReturns.run(uint256 flags, uint256 input)` writes `r = step(prior + input)`, a
  call count and the input to slots 0 to 2, and returns the first `n` of `r`, the count, the prior
  slot 0 and the prior slot 2. The adapter expects `32n` bytes.
- Fixed corpus: 12 scenarios, requiring each arity with both outcomes.
- Decision: a dynamic `bytes` return was probed and not built then, because original Core had no
  variable-length value; the bounded `bytes` return came later. A `memory<DynArray<uint256>>`
  return was rejected before `e2eef194` (Q008) and is accepted since.

### Compare bounded `bytes` returns

`stateful-bytes-returns` returns a `memory<bytes>` value of zero to 64 bytes.

- Convention: `CoreContractEntryProfile.boundedBytesOutcomeV1`. `inLeft unit` is the empty value,
  and `inRight (tag, d0, d1)` the value of length `tag mod 64 + 1` whose data are the first bytes
  of `d0` and `d1`. Every typed value decodes to std's canonical encoding.
- `SynthesizedBytesReturns.run(uint256 flags, uint256 input, uint256 length)` (`0x24b912e5`)
  returns the first `length mod 65` bytes of `d0 = r · K` and `d1 = (count · K) xor last`.
- The source stores them in 96 bytes from `allocate_memory`; std's `abi_encode` zeroes the rest
  of the last Word. The adapter expects `64 + 32⌈L/32⌉` bytes.
- Fixed corpus: 12 scenarios, requiring the lengths 0, 1, 31, 32, 33, 63 and 64.

### Compare returned enums

`stateful-enum-returns` returns a user enum of two to four constructors through `std.ABIGeneric`.

- Convention: `CoreContractEntryProfile.enumOutcomeV1` records each constructor's fields as an
  `EnumPayload` (`noWords`, `oneWord`, `twoWords` or `boundedBytes`). A value is its tag Word with
  its fields, encoded as std does; a dynamic enum gets the offset Word 32 first.
- Constructors are named from a bank without repetition, each with no fields, one or two `uint256`
  or one `memory<bytes>`. A tag is `keccak256("Name(fields)")`.
- `SynthesizedEnumReturns.run(uint256 flags, uint256 input, uint256 choice, uint256 length)`
  (`0x15509d2b`) returns constructor `choice` modulo the count. The adapter computes the tags with
  its own Keccak-256.
- Fixed corpus: 15 scenarios, requiring every position and field kind in static and dynamic enums.

### Compare enum arguments

`stateful-enum-arguments` sends a user enum as a method argument, canonical or with one
malformation, decoded by std's derived decoder. Original Core decodes the calldata itself, without
std's decoder code.

- `SynthesizedEnumArguments.run(uint256 flags, SynthesizedEnum value)`. The selector is std's
  structural signature: `Nil | Single(uint256)` gives `run(uint256,sum(,uint256))`.
- std's decision in order: a short or foreign selector, `0x4924aef0`; a short head or bad dynamic
  offset, `0x08638556`; an unknown tag, empty revert data; a missing field Word or bad `bytes`
  tail, `0x08638556`. Trailing bytes and padding are ignored.
- The selector rule maps Core's selector Word to std's four bytes, and the empty-revert rule its
  Word zero to empty data, each only when it is the prescribed `stdRejection`.
- Malformations: `short`, `selector`, `truncate`, `trailing`, `tag`, `retag`, `offset`, `aliased`,
  `unused`, `tail`, `length` and `padding`. A third of the transactions are canonical.
- Fixed corpus: 21 scenarios, requiring every malformation kind and the three rejections.

### Compare enum arrays

`stateful-enum-array-arguments` sends a calldata array of up to three enums and two indices to
`SynthesizedEnumArrays.run(uint256 flags, SynthesizedEnum[] items, uint256 first, uint256
second)`. The body reads both indexed elements through std's `abiArrayGet`.

- std's decision adds a head shorter than 128 bytes and a bad array offset or length,
  `0x08638556`, and an index of at least the length, `Panic(0x32)`; before solcore-rs `e2eef194`
  it was `ArrayOutOfBounds()` (`0x7f52b2bf`).
- Original Core applies one element decoder to `first`, then `second`. Malformations add `offset`
  and `count` for the array, and `entry` and `share` for an element's table entry.
- Fixed corpus: 17 scenarios, requiring element counts 0 to 3 and the four rejections.

### Compare returned arrays

`stateful-array-returns` returns std's ABI encoding of a memory array of up to three `uint256`,
`bytes4`, `bytes` or `uint256[]` elements.

- The method declares `returns (uint256)`, encodes a `memory<DynArray<t>>` with `abi_encode` and
  ends with the `return_` opcode, as std's `do_exec` does. Reason: before `e2eef194` the checked
  driver refused a declared array output (Q008, `SC0231`). The pin accepts canonical memory
  dynamic-array outputs, which the fixtures `storage-array` and `ufcs-array` and the `T[]` results
  of `runtime-array-abi` use; this profile keeps its encoding.
- Original Core returns the encoding's Words through `wordTupleOutcomeV1`. Arrays of user enums
  stay out, because std has no memory array of multi-Word ADTs.
- The source reads the shape at run time from `length` and `choice`, so that no optimizer folds
  std's encoder loops. The adapter checks the output against its own encoding, padding included.
- Fixed corpus: 23 scenarios.

### Compare constructor arguments

`stateful-constructor-arguments` sends a constructor's parameters after the init code, canonical
or with one malformation, and compares the deployment row before the runtime transactions.

- The derived deployment code copies `codesize() - datasize("<C>Deploy")` bytes into a
  `memory<bytes>` and decodes them through a `MemoryWordReader`, with no up-front head check.
- Original Core runs an initializer contract as the deployment phase, then installs the runtime
  with `Account.withCode`, which keeps the storage. A failed deployment ends the scenario.
- Parameters: none, `uint256`, two `uint256`, `uint256` with up to 64 bytes, or `uint256` with a
  user enum; the constructor writes its record to slots 1 to 5. Malformations: `truncate`,
  `trailing`, `offset`, `length`, `tag`, `tagCut`, `tail` and `narrow`.
- On the EVM a failed creation has no receipt address, so the path binds the would-be CREATE
  address. The keyed runner needs a call, so a scenario without transactions sends a placeholder.
- Fixed corpus: 40 scenarios.

### Compare value forwarded by contracts

`stateful-forwarded-value` has `SynthesizedForwarder` send value to `SynthesizedRecipient` in the
payable `run(uint256 target, uint256 input, uint256 amount)` (`0x24b912e5`). Call value and amount
come from the call-value bank.

- The parent adds the input and its value to slot 0 and calls the child with value `amount`;
  original Core uses `callContractWordWithValue`. `input & 3` chooses whether the child, the root,
  both or neither revert.
- A child revert keeps the amount with the parent; a root revert returns the value to the sender.
  In every committed state the child's balance equals its slot 1.
- The parent's constructor receives 2^72. The Hull runner `rust-hull-forward-scenario` reports a
  rejected transfer as `transfer-rejected`.
- Fixed corpus `scripts/semantic-forward-corpus.json`: 12 scenarios.
- Known finding: two random scenarios crashed O2 code-image export with `Integer overflow when
  casting to usize`; both matched on O0. Recorded in the local `questions.md`.

### Compare call returns

`stateful-call-returns` has a parent call a child method and decode its multi-Word return data
with std's `raw_call` and `abi_decode(ret, @T, @MemoryWordReader)`, which reads from 0 with no
up-front size check.

- No Core host function reads return data, so the parent's reference is in continuation-passing
  form: a call phase and a resume phase that `Solcore/ContractRuntime/CallPhases.lean` runs
  around the child, committing as one transaction.
- Each contract compiles from its own source, so the Yul exporter admits both.
- The child `SynthesizedReturnCallee.get(uint256 x)` (`0x9507d39a`) returns a tuple, `bytes` or an
  enum, typed or raw with one malformation through `return_`. The parent
  `SynthesizedReturnCaller.run` decodes it as the plan's type and writes it to slots 1 to 6.
- Conventions: `wordTupleOutcomeV1`, `boundedBytesOutcomeV1`, `enumOutcomeV1` or the raw
  `rawBytesOutcomeV1` for the child; `wordTupleOutcomeV1` and `wordOutcomeV1` for the phases.
- `rust-hull-call-return-scenario` links the parent with the child's runtime in its code catalog.
  A returned parent's slots must equal the adapter's own decoding of the child's bytes.
- Fixed corpus `scripts/semantic-call-return-corpus.json`: 45 scenarios.

```sh
python3 scripts/semantic-call-campaign.py --profile stateful-call-returns \
  --corpus scripts/semantic-call-return-corpus.json --output .upstream/semantic-call-return-ci
python3 scripts/semantic-suite.py --mode fixed --backend yul \
  --profile stateful-call-returns --output .upstream/semantic-call-return-yul
```

### Compare call sequences

`stateful-call-sequences` has the parent call the child two or three times in one method and read
the latest return data around each call. A compiler that reads a stale buffer, or moves
`returndatasize` or `returndatacopy` across a later call, shows only with several calls.

- The child returns or reverts with the first `L` bytes of three data Words, from the input's
  class byte.
- Around call `k` the parent reads `p_k = returndatasize()` in inline Yul, keeps the call's flag,
  the copy's length `m_k` and its first Word, then reads `n_k = returndatasize()` and a window of
  the data. Each read must see the latest call: `p_1 = 0`, `p_k = m_(k-1)` and `n_k = m_k`.
- Original Core runs the call chain in `CallPhases.lean`, a resume phase after each call; the
  child uses `rawOutcomeV1 2`.
- Fixed corpus: 16 scenarios, among them every boundary input and a de Bruijn sequence of call
  states.

### Compare call branches

`stateful-call-branches` puts the calls in branches and loops, so the input decides whether a
transaction makes zero to three calls. A skipped call leaves the previous buffer, and a looped
call replaces it every iteration; a compiler that caches `returndatasize` or hoists it shows only
here.

- A plan has one to three sites, each a branch or a loop of bound one to three with a stop
  length, with call and exit windows. Input bits choose the calls, and bit 30 reverts the parent.
- Each read must see the latest call made before it, or no buffer before any call.
- Original Core runs the choice chain in `CallPhases.lean`, whose phases request a call or finish.
- A case is 100 to 150 KB, so the call campaign halves its shrink batch as the storage campaign
  does.
- Fixed corpus: 18 scenarios.

### Compare whole committed storage

Every stateful profile compares the observed contracts' whole committed storage after deployment
and after every transaction. Reason: the declared-slot checks missed a stray write by original
Core itself, and any stray write in the two-slot, rollback and two call profiles.

- Histories carry `initialAccountStorage`, an `accountStorage` list per row and
  `finalAccountStorage`: the accounts in role order with their nonzero `{slot, value}` entries in
  increasing slot order. Zero is never listed, so a cleared slot equals an unwritten one.
- Original Core reads `Account.storageEntries`; `Account.mem_storageEntries_iff` proves it lists
  exactly what `storageValue?` returns. Imported Hull reports its committed entries through
  `AccountStorage.canonicalEntries` (`mem_canonicalEntries_iff`, `canonicalEntries_sorted`).
- The EVM path calls `debug_traceTransaction` with `prestateTracer` in diff mode for every
  deployment and transaction and rereads every reported key. A change at another account fails
  closed.
- The diff mode reports exactly the slots whose committed value changes, and a contract starts
  empty, so the reported keys cover the whole storage. Rerun
  `python3 scripts/check-evm-storage-diff.py` after any Anvil change.
- Decision: an `anvil_dumpState` check after every transaction was dropped, because with
  `--steps-tracing` the dump embeds every step trace and outgrew its 64 MiB bound.
- After deployment every storage must be empty, except the constructor-argument profile's record.
  A difference is a `semantic-mismatch` with `accountStorageDifferences` (`{account, slot,
  zeroPaths}`, an undeclared slot shown as `undeclared`). A path whose revert changed its storage
  is listed in `accountStorageRollbackPaths`.
- Fingerprints carry both lists, so a reduction may move a stray write to another undeclared slot
  but not to a declared slot, another account or other paths.
- `--test-field stray`, `parent:stray` or `child:stray` XORs one into slot 2^256 − 2 of one path's
  copied storage; a scenario that declares that slot is rejected.
- History schemas moved to `.v2` for the thirteen profiles that existed then, and the account
  representation changed, so older archives cannot be replayed exactly: rerun their `case.json`.
- Scope: accounts other than the deployed contracts and transient storage are out.

### Compare storage-family contracts on Yul

The twenty-seven storage-family profiles also run with `--backend yul --solc PATH`. They compile
as the pure profiles do: the checked Rust driver's Yul goes through solc
`0.8.35+commit.47b9dedd` with optimization and Osaka. The call-return, call-sequence and
call-branch profiles also run on Yul when selected ([call returns](#compare-call-returns),
[call sequences](#compare-call-sequences), [call branches](#compare-call-branches)).
`stateful-calls` and `stateful-forwarded-value` stay on Sonatina, because each compiles a parent
and a child contract from one source.

- Paths: original Core, the Yul EVM and imported Hull with Sonatina O0 images, recorded in
  `pathBackends` as `original-core`, `yul` and `sonatina-o0`. Hull is an extra reference, not
  Yul-linked execution.
- Each scenario compiles its own Yul after the O0 exports, and the EVM checks the installed
  runtime against the same compilation's deployed bytes.
- The wrappers' runtime code reads no code, and their creation code only its own runtime object,
  so the observations are those on Sonatina. Gas, layout, code size and optimizer internals are
  not compared.
- `export-rust-yul.py` admits the thirty-four pure, the twenty-four storage-family and the two
  call-return wrappers; the three malformed profiles reuse wrappers. Each must compile to one
  creation object with one runtime sub-object and no link or immutable references.
- Exact replay inherits the backend, and a Yul finding is a different identity from the same
  difference on Sonatina.
- The suite runs a storage-family profile on Yul when `--profile` selects it; its default Yul
  selection stays the thirty-four pure profiles.

```sh
python3 scripts/semantic-suite.py --mode fixed --backend yul \
  --profile stateful-storage --profile stateful-methods --output .upstream/semantic-storage-yul
```

### Compare the pinned end-to-end fixtures across paths

`scripts/semantic-fixtures.py` runs the pinned checkout's 184 end-to-end fixtures
(`tests/e2e/*/main.sol`) on four compiled paths. No generator reaches most of their language, and
no original Core exists for them, so the paths are compared with each other and with each
fixture's recorded upstream expectations, and mutated inputs across the paths only. Agreement is
never reported as a Core comparison.

- **Fixtures:** the 184 that `rust-scenario-parity.json` and `rust-method-parity.json` pin by
  source hash: 77 raw scenarios and 107 method-directive fixtures.
- **Paths:** `hull`, checked Hull on Lean Core with Sonatina O0 images; `sonatina-o0` and
  `sonatina-o2` on Anvil; `yul`, the driver's Yul compiled by solc via `export-rust-yul.py
  --fixture`.
- **Environment:** a fresh Osaka chain per fixture with zero base fee and gas price. Method
  directives are rolled-back calls from the zero address, as upstream's `eth_call`; sends persist.
- **Observations:** status, return or revert bytes, ordered logs and, after a successful step,
  every account's whole storage and the contract's and sender's balances.
- **Mutants:** single-change mutants of each recorded call or raw deployment (`--mutants`,
  default 4), each run before its step and rolled back; derived ADT argument mutants at every
  boundary Word of tags, offsets and `bytes` lengths (`--derived-mutants`, default 256); sequence
  mutants that carry one change forward (`commit`, `persist`, `drop`, `duplicate`, `swap`;
  `--sequence-mutants`, default 64); and source mutants, one edit of a literal, operator,
  condition or inline Yul site (`--source-mutants`, default 8).
- **Findings:** a path mismatch, an unmet expectation, a path failure, a compiler crash, or a
  backend refusal while another path compiled (`compile-mismatch`). An unsupported directive,
  compile failure or resource limit excludes the paths that need it. A finding reduces to a
  shortest prefix.
- **Hull memory range:** Hull memory fails for a nonzero-length range ending beyond `2^256 - 32`
  (`Memory.overflowReason`). No EVM transaction can pay for that, so it counts as the Hull path's
  `memory-range` resource limit when every EVM path stopped at a resource limit too.

```sh
python3 scripts/semantic-fixtures.py --output .upstream/fixtures-fixed --jobs 4
python3 scripts/semantic-fixtures.py --mode mutation --seed 20261111 \
  --output .upstream/fixtures-mutation --jobs 4 --reuse-exports
python3 scripts/semantic-fixtures.py --check
python3 scripts/test-semantic-fixtures.py
```

- `--check` verifies the tool receipts and solc and prints the identity of everything a run
  reads. Exports go to `.upstream/semantic-fixtures/<fixture>`; `--reuse-exports` reuses them only
  when every digest matches.
- Lean Core meters fuel, not gas. Each method entry runs in its own Lean invocation within
  `--hull-entry-timeout` (120 seconds), a raw scenario within `--hull-timeout` (600 seconds).
- Fuzz-driver budgets: `--fixture-mutants`, `--fixture-seconds` and `--seconds`. An entry past a
  budget has the status `budget`, which is neither a resource limit nor a finding.
- `report.json` (`solcore-lean.semantic-fixtures.v1`) states `coreReference: false`. The command
  returns 1 for any finding, harness error or changed tool.

Status: at `d1b5ac28` all 184 fixtures compile on every path, and in the fixed run there every
recorded step agreed on all four paths and met its recorded expectation. Known findings:
- Sonatina O2 crashed on `ignored-builtin-effects` at `2a745e12`; `e2eef194` carries upstream's fix.
- The first-allocation class `offset-by-first-allocations`: source mutants whose returned words
  differ exactly where the first allocations differ, Hull and solc at `0x80`, Sonatina O2 at
  `0x140` and O0 at `0x200`.
- Two Yul stores moved to `2^256 - 1` fail Hull memory's range and run Sonatina out of gas, while
  solc's Yul drops the store and returns. The fuzz driver lists this as known.

### Compare pure cases on Lean's native frontend

`scripts/semantic-native.py` takes the pure runner's own cases, the fixed corpora or a draw seeded
as `semantic-suite.py` seeds it (`--mode random --seed N`), and runs each admitted case through
`semantic-native-tool`. The case's source is lifted out of its contract by `native-lift-v2`, which
keeps its imports of `std.opcodes` and drops std's other imports, a Word entry for its method is
appended, and the program is compiled once and run once per input. The path is opt-in: no suite
or CI job runs it, and the fuzz driver runs it only with
`--backend native` ([continuous fuzzing](SEMANTIC_CI.md#continuous-fuzzing)).

- **Admission** (`native-admission-v4`) is decided from the case alone, before any native run: its
  emitter, the Core operations of its program, and the adapter's reading of the source, which
  must be one contract with functions only, no storage field, `uint256` parameters and no call
  of std's `tobool`. A memory-array source must not use std's array traits or a literal `lidx`
  index. Cases that are not admitted are counted by reason.
- **Comparison** (`native-compare-v1`): a returned Word against direct Core's, and the revert data
  of a native panic, which the native session decodes, against direct Core's revert output. Out of
  fuel and timeouts are inconclusive.
- **Findings.** A native rejection, a crash or a different observation of an admitted case is a
  finding under a stable signature, with a request that `semantic-native-tool` replays. The known
  differences from upstream (row 1's open `Typedef` call, which also rejects an unannotated
  `let m = [];`, row 4's array operations on an open base, local lambda generalization, `bool ==`,
  `!=` at types without a builtin, reads of uninitialized locals) are findings under their own
  labels.
- `--check` prints the identity of every tool, script and corpus a run reads. A run whose identity
  changes while it runs does not pass.

```sh
lake build semanticNativeTool
python3 scripts/semantic-native.py --output .upstream/semantic-native
```
