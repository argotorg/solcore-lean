# Generated semantic comparisons

The implementation plan and completion criteria are in
[Semantic differential testing milestones](../docs/design/semantic-differential-testing.md).
The reference Rust revision remains `2a745e12974c373c3799fec81b48a53c7dce2ab4`.

## Generate and inspect source cases

Build the native tools once:

```sh
lake build semanticCaseTool rustHullContract rustHullScenario
```

The first source emitter supports checked, closed G0 Word programs with Boolean
subexpressions, local Word bindings, conditionals, Boolean and Word negation,
addition, subtraction, multiplication, bitwise and/or/xor, equality and unsigned
greater-than. Unsupported operations are explicit exclusions, including in
branches that would not execute. The original Core generator is unchanged.

Generate twelve cases with a 24-node budget, at most 2,000 attempts, and one
million Core execution steps per case:

```sh
mkdir -p .upstream/semantic-cases
.lake/build/bin/semantic-case-tool generate 0 24 12 2000 1000000 > .upstream/semantic-cases/corpus.json
```

The arguments are `SEED NODES COUNT ATTEMPTS FUEL`. Seed search uses consecutive
64-bit seeds beginning at `SEED`. Every attempted seed and exclusion contributes
to the reported counts. Inspect the corpus `status`: `generation-exhausted`
means the requested number of supported cases was not produced, even if the
tool successfully wrote its report. It is not a successful test campaign.

Each case contains the original Core Wire program, emitted source, versioned
provenance, contract metadata and a fresh direct Core observation. The wrapper
is `SynthesizedG0.run()`, returning a single ABI `uint256` with no inputs.

The same tool accepts:

```text
semantic-case-tool emit PROGRAM.json [FUEL]
semantic-case-tool observe CASE.json [FUEL]
semantic-case-tool replay CASE.json [FUEL]
semantic-case-tool shrink CASE.json LIMIT [FUEL]
```

`emit` checks an externally supplied Core Wire program against G0 before
rendering it. `observe` evaluates its original Core expression. `replay`
rechecks the program, regenerates seeded cases, compares source and wrapper
metadata, and computes the result again. A saved `directCore` field is never a
trusted expected result. `shrink` returns checked, smaller, re-emitted
candidates; it does not by itself establish that any candidate preserves an
observed mismatch.

Generation is bounded to 512 nodes, 1,024 requested cases and 10,000 attempts per
invocation. The seed must be an exact unsigned 64-bit decimal integer. Explicit
case-tool fuel is at most 10,000,000. Corpus generation never silently replaces
an unsupported expression with a different computation.

## Validate the emitter against Rust

Prepare the checked Hull exporter as described in
[Rust runtime compatibility checks](RUST_PARITY.md). Then run:

```sh
python3 scripts/test-source-synthesis-rust.py
```

The default validation checks 27 explicit operation, boundary-value and scope
cases, plus twelve generated cases. Each emitted source passes the actual
public Rust checking pipeline. Its imported Hull then executes through the
native Core contract runner and must return exactly the ABI encoding of the
original Core result. Temporary source files and exports are removed at the end.

This command does not execute an EVM. It verifies source acceptance and the
imported-Hull path; it is not the complete three-path differential campaign.
The emitter's meaning preservation has not been formally proved. Core typing
of admitted generated/reduced programs is established by the existing checker
soundness theorem.

Closed G0 computations can be folded during Rust specialization or optimization.
Source-feature coverage therefore does not imply execution of those arithmetic
opcodes in the resulting bytecode. A runtime-input profile is needed to make a
separate backend opcode-coverage claim.

## Validation and retained artifacts

The emitter and case-tool regressions are registered in `Tests/Main.lean`.
They check full-width values, scope, branch-local computations, unsupported
operations, replay tampering, fuel exhaustion and checked reduction candidates.

Keep regression cases and replay metadata that explain a finding. Remove
disposable verification exports and logs after recording the results. Never
count source rejection, missing execution or resource exhaustion as agreement.
Core execution fuel and EVM gas have separate meanings and budgets.

## Compare one case on all three paths

Install the pinned-compatible Anvil toolchain and build the Rust code-image
exporter as described in [RUST_PARITY.md](RUST_PARITY.md). The runner starts its
own loopback-only Anvil and needs an environment that permits local listening
sockets. It never uses an existing chain or a remote RPC endpoint.

Extract one generated case from the corpus above:

```sh
python3 - <<'PY'
import json
from pathlib import Path
root = Path('.upstream/semantic-cases')
corpus = json.loads((root / 'corpus.json').read_text())
assert corpus['status'] == 'complete' and corpus['cases']
(root / 'case.json').write_text(json.dumps(corpus['cases'][0], indent=2) + '\n')
PY
python3 scripts/semantic-differential.py \
  --case .upstream/semantic-cases/case.json \
  --output .upstream/semantic-cases/run
```

The output directory must be new. A run rechecks and re-emits the case, computes
the original Core result, compiles checked Rust Hull and exact Sonatina O0
images, deploys those bytes on Anvil, and executes the same imported contract
through Core. Every passing run has three completed observations and three
matching pairwise comparisons. No saved expected result is trusted.

The result is `report.json`. It records tool versions and hashes, pinned
compiler/exporter receipts, source and artifact hashes, deployment and call
inputs, budgets, process outcomes, raw observations and normalized comparisons.
It preserves a valid returned payload of the wrong ABI length as an observable
semantic mismatch; malformed transport remains an adapter error.

Replay the complete archive into another new directory:

```sh
python3 scripts/semantic-differential.py \
  --replay .upstream/semantic-cases/run \
  --output .upstream/semantic-cases/replay
```

Replay verifies all recorded archive members, rejects missing or changed files
and tool drift, restores the saved budgets, and performs fresh executions.
To deliberately change budgets or tools, use the saved `case.json` with
`--case` instead. This starts a new experiment rather than an exact replay.

Useful limits are `--direct-fuel`, `--core-fuel`, `--gas`, `--timeout`,
`--total-timeout`, `--output-limit` and `--artifact-limit`; see `--help` for
defaults. The runner exits zero only for `matched`. Rejection, compiler crashes,
execution errors, semantic mismatches, unsupported scope and inconclusive
resource limits remain distinct in the report. In particular, insufficient
deployment gas does not count as a mismatched return value.

Run the runner's protocol and resource regressions with:

```sh
python3 scripts/test-semantic-differential.py
```

These include real child-process timeouts/output limits and artifact tampering.
They complement actual Anvil integration; unit tests alone do not establish
that all three execution paths ran.

## Run a bounded campaign

Run the fixed corpus after building the tools and exporters above:

```sh
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-corpus.json \
  --output .upstream/semantic-ci \
  --seconds 300 --disk-bytes 134217728
```

The manifest fixes sixteen seed/node-budget pairs and their expected versions
and AST features. Its required coverage includes every enabled operation,
bindings, branches, and Word literals zero, one, maximum and the high bit. Only
cases that actually match across all three paths contribute to passing
coverage. This is source AST coverage, not runtime opcode coverage.

For a seed search instead of the fixed corpus:

```sh
python3 scripts/semantic-campaign.py \
  --seed 78 --nodes 32 --cases 16 --attempts 256 \
  --output .upstream/semantic-search \
  --seconds 300 --disk-bytes 134217728 --shrink-attempts 32
```

`--attempts` bounds generation attempts. `--shrink-attempts` bounds candidate
executions across the entire campaign, and `--shrink-candidates` bounds each
candidate batch. Core fuel, EVM gas, per-case time, total campaign time and
retained directory size have separate limits. Time and disk usage are checked
during child-process execution; these are polling limits, not OS quotas.
An interrupt or SIGTERM stops owned children and writes the campaign summary.

The command prints per-case results and a final summary. `summary.json` records
generated, excluded, executed, completed, matched, mismatched, inconclusive,
error and unexecuted counts, with source/compiler rejections counted separately
within errors. Generation exhaustion, incomplete coverage and interrupted or
resource-limited runs never pass. Exit zero requires every requested case to
match and every required coverage item to be present.

All generated cases and compact execution reports remain in `cases/` and
`results/`. Successful runs' large exports and logs are removed. These compact
reports retain receipts and observations but cannot serve as exact archives;
use their saved case with `--case` to execute a new experiment.

Each finding retains complete original and final reduced archives under
`findings/`, plus `shrink.json`. A candidate must retain the failure category,
stage, disagreeing paths, and each path's outcome and payload form. A wrong
return value cannot shrink into a revert or a resource failure. Other genuine
findings encountered during reduction are retained separately, without recursive
reduction. Exact replay uses the single-case runner's `--replay ARCHIVE` option.

## Check the reducer

The explicit test adapter below perturbs a copied observation only after all
three real executions agree:

```sh
python3 scripts/semantic-campaign.py \
  --seed 78 --nodes 32 --cases 1 --attempts 1 \
  --test-perturb-path rustEvm --shrink-attempts 8 \
  --output .upstream/semantic-reducer-test
```

This command intentionally exits nonzero. Its synthetic findings are marked
and stored separately from genuine findings. The actual execution reports are
unchanged; the changed observation exists only in `analysis.json`. Reproduce
the reduced synthetic finding with `--case` and the same explicit adapter:

```sh
python3 scripts/semantic-campaign.py \
  --case .upstream/semantic-reducer-test/findings/synthetic/0000/reduced/case.json \
  --test-perturb-path rustEvm --shrink-attempts 0 \
  --output .upstream/semantic-reducer-replay
```

Without the adapter, that case's three real results still match. This tests
detection, preservation and reduction of a controlled difference; it is not
evidence of an upstream compiler bug.

Focused campaign tests and independent corpus validation are available with:

```sh
python3 scripts/test-semantic-campaign.py
python3 Tests/scripts/test-semantic-corpus.py
```

The corpus validator checks deterministic materialization, native Core
execution, replay and AST coverage. It does not execute the EVM. The complete
campaign above executes all three paths for every passing corpus case.

## Compare functions with runtime inputs

The `runtime-word` profile is the first M4 extension. It keeps the closed G0
generator and saved cases unchanged. The original Core program applies a checked
Word-to-Word lambda to one recorded Word. Its Solcore source accepts that same
Word through `SynthesizedInput.run(uint256)`, so changing the input does not
change the function's source. Each input is a separate comparison case and
currently has its own compilation and deployment.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-word --seed 78 --nodes 32 --cases 8 --attempts 256 \
  --output .upstream/semantic-runtime-inputs
```

Generation abstracts one Word literal from a G0 expression without capturing
local variables. It evaluates the resulting Core function at zero, one, maximum
Word and the high bit, and accepts the function only if all four return and at
least two results differ. One accepted function supplies up to four cases in
that order. `--attempts` counts function candidates; `--cases` counts individual
input comparisons. The final function's inputs may be truncated by that limit.
Generation fuel failures appear in `generationResourceExclusions` as a subset
of `excluded`, separately from executed-case resource failures.

Native commands are:

```text
semantic-case-tool input-generate SEED NODES COUNT ATTEMPTS FUEL
semantic-case-tool input-emit FUNCTION.json INPUT [FUEL]
```

`FUNCTION.json` is a Core Wire program containing a closed Word-to-Word lambda.
`INPUT` is a canonical unsigned decimal Word. Imported and reduced functions
may be constant; the input-sensitivity requirement is a generation filter.
The existing `observe`, `replay` and `shrink` commands recognize both case
schemas. Replay checks the original Core argument, ABI calldata, function,
source and versioned generation provenance. It recomputes observations rather
than trusting saved results. Generated cases retain their generation validation
fuel independently of a replay's execution budget.

The runtime corpus checks inputs separately from constants in the program:

```sh
python3 Tests/scripts/test-semantic-corpus.py --manifest scripts/semantic-input-corpus.json
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-input-corpus.json \
  --output .upstream/semantic-input-ci
python3 scripts/test-source-input-rust.py
```

For runtime manifests, `requiredInputs` is satisfied only by inputs whose three
executions agree. `generatedInputs`, `matchedInputs` and `missingInputs` report
that coverage. `requiredWordLiterals` still measures literal presence in the
Core AST, including an application's argument; it cannot establish input
coverage. The fixed functions cover identity, unsigned boundary branches,
nested local scopes and generated bodies. They do not claim all richer M4
features or measured EVM opcode coverage.

The external input regression executes two unchanged source functions at all
four boundary inputs, checks three-way agreement and varying results, and
replays a saved input-dependent run. The input profile also supports automatic
reduction of its function body and input while retaining the checked application
form. Named functions, private mutable locals, aggregates and bounded loops
extend this workflow below.

## Compare acyclic named functions

The `runtime-functions` profile adds one to three named Word-to-Word helpers.
Each helper can call earlier helpers; an entry function receives the ABI Word
and returns a Word. The original Core program retains the complete chain of
helper lambdas and applies the resulting entry closure to the recorded input.
Source emission uses top-level named functions and
`SynthesizedFunctions.run(uint256)`. Recursive or escaping function values and
references to host bindings are outside this profile.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-functions --seed 31 --nodes 96 --cases 8 --attempts 256 \
  --output .upstream/semantic-functions
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-function-corpus.json \
  --output .upstream/semantic-function-ci
python3 scripts/test-source-function-rust.py
```

Native entry points are `function-generate SEED NODES COUNT ATTEMPTS FUEL` and
`function-emit FUNCTION.json INPUT [FUEL]`. Observe, replay and shrink dispatch
by the saved schema. Node limits apply to the entire original Core application,
including all helper definitions. Generation attempts count function graphs;
each accepted graph supplies the same four ordered boundary inputs as the
single-function profile. Generated graphs call every earlier helper in a
chain; imported graphs can also share callees, as in the diamond fixture.

The fixed corpus includes chains, a diamond and generated graphs with one,
two and three helpers. It tracks `requiredHelperCounts` separately from input
coverage. `matchedHelperCounts` records declaration counts for cases whose
three results agree. It is not a count of runtime calls or EVM call instructions.
Body feature coverage includes `functionCall`, without counting the compiler's
wrapper lambdas as source function definitions.

Reduction keeps helper declarations in their original order and checks the
complete graph after every candidate body or input change. The first reducer
keeps the number of helpers fixed; it can remove calls or simplify bodies but
does not delete and reindex declarations. Private mutable locals, aggregates
and bounded loops extend this workflow below.

## Compare private mutable locals

The `runtime-mutation` profile keeps the Word-only ABI and one to three acyclic
Word helpers. Each helper may allocate private Word cells, read and update them,
and sequence Unit results through locals and branches. Cell aliases, escaping
cells and non-Word cells are excluded. The original Core graph retains real
allocations, loads and stores; the source uses mutable Word locals in
`SynthesizedMutation.run(uint256)` and its helpers.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-mutation --seed 57 --nodes 192 --cases 4 --attempts 256 \
  --output .upstream/semantic-mutation
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-mutation-corpus.json \
  --output .upstream/semantic-mutation-ci
python3 scripts/test-source-mutation-rust.py
```

Native commands are `mutation-generate SEED NODES COUNT ATTEMPTS FUEL` and
`mutation-emit FUNCTION.json INPUT [FUEL]`. Replay and shrinking use the saved
case schema. The campaign's default node limit is 192 for this profile; the
512-node hard limit still applies to the complete applied function graph.
Versioned templates combine checked G0 scalar expressions with ordered stores,
Unit branches, two independent cells and a load followed by a later update.
Each accepted graph must return distinct values at two or more boundary inputs.

Every source read is captured before subsequent effects. Unit sequencing
binders remain in the renderer's context even when no source declaration is
needed. Reduction preserves the typed binder inventory and helper declarations,
rechecks the whole graph and requires smaller candidates. It may simplify store
values or replace a store with Unit without deleting its surrounding binder.

The fixed 28-case corpus contains seven graphs at all four boundary inputs. All
cases match across the three actual paths. Coverage includes fourteen AST
feature kinds, helper counts one through three and all four inputs. A separate
`recipeCoverage` section records the four generator templates and update counts
one through four. Matched recipe coverage requires native replay and three-way
agreement; it measures generator metadata, not dynamic branches or instructions.
The fixed manifest's recipe requirements are enforced alongside AST/input/helper
coverage. A separate twelve-case external regression checks read-before-write
snapshots, independent cells and callee isolation, followed by exact replay.

## Compare internal pairs, sums and matches

The `runtime-aggregates` profile admits internal `(word, word)` pairs and
`sum<word, word>` values, projections, and two-way matches. It combines them
with the existing scalar operations, private Word cells and acyclic helpers.
The ABI remains `SynthesizedAggregates.run(uint256)` with Word-only arguments
and results. Nested aggregate types, aggregate cells and escaping cell values
are outside this profile.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-aggregates --seed 21 --nodes 256 --cases 4 --attempts 256 \
  --output .upstream/semantic-aggregates
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-aggregate-corpus.json \
  --output .upstream/semantic-aggregate-ci
python3 scripts/test-source-aggregate-rust.py
```

Native commands are `aggregate-generate SEED NODES COUNT ATTEMPTS FUEL` and
`aggregate-emit FUNCTION.json INPUT [FUEL]`. The campaign defaults to 256 nodes
for this profile; its hard limit remains 512 nodes for the complete applied
graph. Fixed seeds use individual budgets within that limit. Unsupported G0
scalar operations still produce explicit exclusions.

Pair operands evaluate left to right and retain their values across later
writes. Projections and sum scrutinees evaluate once. The emitter uses tuple
patterns for projection and sum patterns for branch selection. It retains Core
payload, Unit and local binding positions independently of fresh source names.
Reduction preserves distinct left/right payload markers as well as typed let
bindings. It cannot extract a branch body and silently drop its payload binder.

The fixed 32-case corpus has eight graphs at all four boundary inputs. All
cases agree across the three actual paths. Eighteen AST feature kinds, helper
counts one through three and all four generator templates are covered. Recipe
requirements use `templates: [0, 1, 2, 3]` and `updates: []`; this profile has no
update-count recipe dimension. Coverage is still AST/metadata coverage.
The separate sixteen-case external suite checks retained aggregate snapshots,
single evaluation of projections, nested payload/helper effects and typed
pair/sum branch results, then replays a saved run exactly.

## Compare bounded loops

The `runtime-loops` profile retains a checked aggregate step graph and a mask.
Its source runs `while (limit > counter)` with `limit = input & mask`, updating
an accumulator through the arbitrary step entry on each iteration. The original
Core reference captures that entry closure once and executes a finite sequence
of literal-ordinal guards and accumulator stores. It does not reuse the source
counter implementation. The ABI is `SynthesizedLoops.run(uint256)`.

```sh
python3 scripts/semantic-campaign.py \
  --profile runtime-loops --seed 21 --nodes 384 --cases 6 --attempts 256 \
  --output .upstream/semantic-loops
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-loop-corpus.json --seconds 600 \
  --output .upstream/semantic-loop-ci
python3 scripts/test-source-loop-rust.py
```

Native commands are `loop-generate SEED NODES COUNT ATTEMPTS FUEL` and
`loop-emit PLAN.json INPUT [FUEL]`. A plan has schema
`solcore-lean.loop-plan.v1`, a `stepProgram` containing a checked aggregate
function DAG, and an integer `mask` in zero, one, three or seven. Saved cases
contain both `loopPlan` and the actual applied original Core `program`. Native
admission reconstructs and checks their exact correspondence for every origin.
The complete applied reference has a 512-node limit; generation defaults to 384.

Each accepted seed supplies six ordered inputs: zero, one, three, seven,
maximum Word and the high bit. Generation selects masks one, three or seven,
requires an input-sensitive step, and checks that at least one positive-trip
input changes its value. Imported and reduced plans may be identity functions
or use a zero mask. Reduction preserves step binders and helper count, rebuilds
the complete reference, and requires strict decrease of its complexity.

The fixed corpus has eight plans at all six inputs, with all 48 cases matching
across the three actual paths. It covers nineteen step AST features, one to
three step helpers and all four aggregate recipes. `loopRequirements` declares
required `masks` and `iterations`; the fixed values are zero, one, three and
seven for each. `loopCoverage` derives prescribed iterations from the validated
input and mask and counts only three-way matches toward passing coverage. It
does not claim measured execution traces. Helper coverage excludes the emitted
`sc_step` and ABI wrappers. Features describe the step graph; full-program
literal coverage remains separate.

The external 24-case suite checks zero and positive iterations, arbitrary step
entries, pair/sum branches, fresh helper-local cells per iteration and Word
wrap, followed by exact replay.

## Compare ordered storage transactions

The M5a execution connection uses a separate storage case format and runner.
`SynthesizedStorage.run(uint256)` reads slots zero and one, applies a checked
aggregate step to `input + old0`, writes its result to slot zero, increments
slot one, and returns the sum of both reread slots. Each scenario starts with
empty storage. Generated scenarios contain three ordered transactions;
imported and reduced scenarios may contain one through three.

Build the two native tools and generate a small corpus:

```sh
lake build semanticStorageTool rustHullStorageScenario
mkdir -p .upstream/semantic-storage-cases
.lake/build/bin/semantic-storage-tool generate 0 256 2 64 1000000 \
  > .upstream/semantic-storage-cases/corpus.json
```

Generation arguments are `SEED NODES COUNT ATTEMPTS FUEL`; `COUNT` counts
scenarios. Check that the corpus `status` is `complete` before using it as a
completed batch. Native entry points are:

```text
semantic-storage-tool emit PLAN.json TRANSACTIONS.json [FUEL]
semantic-storage-tool replay CASE.json [FUEL]
semantic-storage-tool observe CASE.json BINDINGS.json [FUEL]
semantic-storage-tool shrink CASE.json LIMIT [FUEL]
```

A plan has schema `solcore-lean.storage-plan.v1` and a `stepProgram` containing
a checked aggregate function DAG. Transactions are an ordered JSON array of
`{id, input, calldata, value}` objects: IDs are distinct bounded identifiers,
inputs are canonical decimal Words, calldata is selector `0xa444f5e9` followed
by that Word's 32-byte encoding, and value is `"0"`. The saved
`solcore-lean.semantic-storage-case.v1` contains one original host-aware Core
contract, its emitted source, plan, transactions and versioned provenance.
It contains no expected execution result. Replay reconstructs the exact
contract, checks emission and metadata, and validates generated or reduced
origins. Shrinking preserves helper/binder scope and transaction ID order while
simplifying the step, inputs or sequence; candidates still need execution to
establish that they preserve a finding.

`observe` executes the original checked contract through `ContractRuntime`.
Bindings have schema `solcore-lean.storage-bindings.v1` with distinct decimal
`caller` and `address` fields. The comparison runner records the actual Anvil
bindings in `bindings.json` and supplies them to both Core paths. Each invocation
uses the same installed code and a fresh local heap; only its terminal
`finalWorld` becomes the next transaction's world.

Extract and compare one scenario, then replay its archive:

```sh
python3 - <<'PY'
import json
from pathlib import Path
root = Path('.upstream/semantic-storage-cases')
corpus = json.loads((root / 'corpus.json').read_text())
assert corpus['status'] == 'complete' and corpus['cases']
(root / 'case.json').write_text(json.dumps(corpus['cases'][0], indent=2) + '\n')
PY
python3 scripts/semantic-storage-differential.py \
  --case .upstream/semantic-storage-cases/case.json \
  --output .upstream/semantic-storage-cases/run
python3 scripts/semantic-storage-differential.py \
  --replay .upstream/semantic-storage-cases/run \
  --output .upstream/semantic-storage-cases/replay
```

Both output directories must be new. The runner compiles checked Rust Hull and
linked Sonatina O0 images, verifies the deployed runtime bytes, and sends actual
transactions on its owned local Anvil. Return bytes come from each mined
transaction's trace; slot snapshots come from `eth_getStorageAt` at that
receipt's block. The separate Hull runner reports committed slots explicitly,
including when a receipt has no world, and stops on incomplete execution.
An uncertain transaction submission is never retried automatically.

A pass requires agreement on empty initial storage and on status, return bytes
and committed slots after every transaction, across all three path pairs. A
later resource failure cannot erase an already observed prefix mismatch. Exact
replay checks archive members, tool identities and saved budgets, then starts a
fresh deployment and recomputes all observations.

```sh
python3 scripts/test-semantic-storage-differential.py
python3 scripts/test-source-storage-rust.py
```

The 34 protocol regressions pass. The external suite passes six scenarios and
fifteen actual transactions, followed by exact archive replay. It covers
feedback, repeated inputs, single-call sequences, sparse zero storage, clearing
and rewriting a slot, fresh private cells, arbitrary entries and aggregate
branches. Changing the input sequence leaves the original Core contract and
source unchanged. Full repository build/tests and the kernel policy check pass.

This first storage profile admits valid `run(uint256)`
inputs, zero call value, initially empty literal slots zero and one, and
successful Word returns. The rollback profile below extends completion
behavior; bounded external calls use the separate profile below. This scope
does not establish equivalence of arbitrary storage, gas, balances, nonce,
logs, account lifecycle or the source emitter itself.

## Run and reduce storage campaigns

Run the fixed stateful corpus or generate a bounded batch:

```sh
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-storage-corpus.json \
  --output .upstream/semantic-storage-ci --seconds 600
python3 scripts/semantic-storage-campaign.py \
  --seed 3 --nodes 384 --cases 4 --attempts 256 \
  --output .upstream/semantic-storage-search --seconds 600
python3 Tests/scripts/test-semantic-storage-corpus.py
python3 scripts/test-semantic-storage-campaign.py
```

All ten fixed scenarios and 27 transaction prefixes match across the actual
three paths. The manifest requires nineteen step AST features, six boundary
inputs, one through three declared helpers and transactions, and all four step
generator templates. Only fully matched scenarios count toward passing
coverage. The native corpus validator checks materialization, strict replay and
repeat observations; it does not execute an EVM.

The summary counts scenarios separately from transactions observed on any path,
completed on all three paths, and matched ordered prefixes. Shrink executions
are excluded from these transaction counts. The campaign enforces generation,
case, total time, disk and reduction limits. Successful runs retain compact
receipts and input cases; their exports are removed. Use `--case` with a saved
case for a new experiment. Findings retain full original and final archives
for `semantic-storage-differential.py --replay`.

Reduction can simplify the checked step, reduce runtime inputs or remove
transactions. The failure fingerprint uses a stable transaction ID rather than
its sequence index, and preserves the differing fields/slots, disagreeing paths
and outcome/payload forms. Candidate identity includes both the original Core
program and the transaction sequence. Every accepted candidate has been
rechecked and rerun on all three paths.

To exercise reduction deliberately, use an explicit copied-observation adapter:

```sh
python3 scripts/semantic-storage-campaign.py \
  --case .upstream/semantic-storage-cases/case.json \
  --test-perturb-path importedHull --test-transaction-id tx-1 \
  --test-field storage:1 --shrink-attempts 12 \
  --output .upstream/semantic-storage-reducer --seconds 600
```

This changes a copied observation only after actual agreement. Raw reports
remain unchanged, and the command exits nonzero for the synthetic mismatch.
`--test-field` accepts `output`, `storage:0` or `storage:1`. A selected transaction
removed by a candidate cannot preserve that synthetic finding. The integrated
check reduced three transactions to only `tx-1`, retained the same fingerprint,
and passed both fresh actual archive replay and synthetic replay. Genuine
findings discovered while shrinking are retained separately.

## Compare rollback after storage writes

The `stateful-storage-rollback` profile keeps the two-slot feedback protocol and
uses `SynthesizedRollback.run(uint256)`. Both writes and the final slot reads
execute before the original ABI input selects completion: an odd input reverts
with the tentative slot sum encoded as exactly 32 bytes; an even input returns
that same Word. A reverted call retains the immediately preceding committed
world, while its output describes the tentative computation. A zero payload
still contains 32 bytes.

The original Core contract uses the existing typed `wordOutcomeV1` convention.
`ContractRuntime` selects the committed or rolled-back world; the Core wrapper
does not restore storage itself. The source emits `mstore(0, result)` followed
by `revert_(0, 32)` in the odd-input branch. The comparison requires matching
status, payload and committed storage at every prefix, and independently checks
that each reverted snapshot equals its predecessor.

Build the new native case tool:

```sh
lake build semanticStorageRollbackTool rustHullStorageScenario
```

`semantic-storage-rollback-tool` provides the same `generate`, `emit`, `replay`,
`observe` and `shrink` commands as the storage tool above. Its plan schema is
`solcore-lean.storage-rollback-plan.v1`, and its case schema is
`solcore-lean.semantic-storage-rollback-case.v1`. Generated scenarios use an
even/odd/even sequence and must complete as return/revert/return under actual
Core execution. Imported and reduced scenarios may have any parity pattern
within the one-to-three transaction limit. Existing successful-storage cases
retain their own schema, source and completion policy.

The same comparison and campaign scripts select the native tool and completion
rules from the saved case or corpus profile. Use
`--profile stateful-storage-rollback` for a seed search. The storage runner enables Anvil's
`--steps-tracing`: a failed receipt counts as an explicit revert only when its
trace confirms terminal `REVERT`, after resource errors have been excluded.
Out-of-gas, fuel exhaustion and exceptional failure never become matching
rollbacks. Archive replay retains the usual tool-hash and budget checks.

```sh
python3 scripts/test-source-storage-rollback-rust.py
python3 Tests/scripts/test-semantic-storage-corpus.py \
  --manifest scripts/semantic-storage-rollback-corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-storage-rollback-corpus.json \
  --output .upstream/semantic-storage-rollback-ci --seconds 600
```

The external suite passed eight scenarios and 21 actual transactions, including
twelve returns and nine reverts, followed by exact archive replay. Cases cover
success/revert/success, consecutive reverts, an initial all-zero revert payload,
rollback of a tentative slot deletion, fresh private cells, arbitrary entries,
aggregate branches and zero writes. The original Core contract and source stay
fixed when transaction inputs change.

The fixed twelve-scenario corpus passed native materialization, replay and all
33 transactions. It covers twenty step AST features, the six boundary inputs,
one through three declared helpers and transactions, and all four generator
templates. `requiredOutcomes` and `requiredCompletionPatterns` add coverage for
both return/revert and four ordered completion patterns, measured from completed
histories. This native validator does not execute the EVM. The separate actual
campaign also passed all twelve scenarios and 33 prefixes, with complete
coverage. The ten-scenario M5a campaign still passed all 27 prefixes with step
tracing enabled.

A copied reverted-payload difference at `tx-1` accepted nine reductions in
twelve candidate executions, leaving only the same reverting transaction.
Every actual candidate report matched. Exact archive replay and fresh synthetic
replay reproduced actual agreement and the same synthetic failure fingerprint.
For this profile, a reducer cannot preserve a reverted-payload finding by
turning it into a normal return, an empty payload or resource exhaustion.

Full repository build/tests and kernel policy passed, along with forty storage
protocol and 24 campaign regressions. The rollback profile retains the initially
empty two-slot domain, valid Word calldata and zero call value.

## Compare bounded parent/child calls

The `stateful-calls` profile installs `SynthesizedCaller` and
`SynthesizedCallee`. The parent's empty payable constructor receives eight units
of value; the child's deployment receives zero. Both begin with empty storage.
Original Core starts from that declared post-deployment world; it does not
execute the source constructors. Rust EVM and imported Hull execute the actual
deployments, and the runner checks their resulting initial accounts.

Each of one to three zero-value transactions calls
`SynthesizedCaller.run(uint256 target, uint256 input)`, selector `0x7357f5d2`.
The parent receives 68 bytes including the selector. It calls the payable child
fallback with one raw 32-byte Word. The source reserves scratch memory through
the free-memory pointer and rejects child returndata that is not exactly 32
bytes. The fixed protocol uses the low three input bits:

| Mask | Prescribed behavior |
| --- | --- |
| `1` | Child reverts after its storage writes and topic-two log. |
| `2` | Parent reverts after consuming the child outcome and writing/logging its result. |
| `4` | Parent sends value one to the child; otherwise it sends zero. |

The parent increments slot zero by the input and logs topic one. The child
applies the checked aggregate step to `input + oldChild0`, writes that result
to slot zero, increments slot one, and logs topic two. The parent writes the
child payload to slot one, adding one if the child reverted, then logs topic
three. Its root payload is the sum of both parent slots. Each return/revert
payload is one big-endian Word. Unexpected call failures are exceptional exits.

Build the separate native tools and generate a case:

```sh
lake build semanticCallTool rustHullCallScenario
mkdir -p .upstream/semantic-call-cases
.lake/build/bin/semantic-call-tool generate 1 243 1 1 1000000 \
  > .upstream/semantic-call-cases/corpus.json
python3 - <<'PY'
import json
from pathlib import Path
root = Path('.upstream/semantic-call-cases')
corpus = json.loads((root / 'corpus.json').read_text())
assert corpus['status'] == 'complete' and corpus['cases']
(root / 'case.json').write_text(json.dumps(corpus['cases'][0], indent=2) + '\n')
PY
python3 scripts/semantic-call-differential.py \
  --case .upstream/semantic-call-cases/case.json \
  --output .upstream/semantic-call-cases/run
python3 scripts/semantic-call-differential.py \
  --replay .upstream/semantic-call-cases/run \
  --output .upstream/semantic-call-cases/replay
```

The native tool also provides:

```text
semantic-call-tool emit PLAN.json TRANSACTIONS.json [FUEL]
semantic-call-tool replay CASE.json [FUEL]
semantic-call-tool observe CASE.json BINDINGS.json [FUEL]
semantic-call-tool shrink CASE.json LIMIT [FUEL]
```

Plans use `solcore-lean.call-plan.v1` with a checked aggregate `stepProgram`.
Cases use `solcore-lean.semantic-call-case.v1` and retain both original Core
programs. The combined programs are limited to 512 nodes; the fixed wrappers
add 179 nodes to the step. Transactions contain a stable `id`, decimal `input`,
`value: "0"`, `target: "parent"` and `callee: "child"`. The source and programs
remain fixed across input sequences. Actual decimal caller/parent/child
addresses arrive through `solcore-lean.call-bindings.v1`. They must be distinct;
contract addresses zero through 17 and 256 are excluded at the Osaka boundary.
Cases never embed an invented deployment address or a saved expected result.

Original Core runs through `OneLevelNestedExecution.run`, retaining only the
terminal committed world between transactions and starting fresh private heaps.
The Rust path mines transactions, reads their output from step-enabled traces,
and obtains both accounts' slots zero/one and balances at each receipt block.
Committed logs come from receipts. Imported Hull uses the same actual bindings
and exact linked runtime images. A pass requires matching initial accounts and
every completed prefix: root status/payload, both account snapshots and ordered
logs. Root rollback must restore both prior snapshots and remove committed
logs; child rollback can leave earlier parent effects intact. Unknown submission
outcomes are not retried. Fuel, gas and process limits remain distinct.

Exact archive replay checks saved artifact and executable hashes before fresh
execution. Rebuilding a native tool or changing an adapter invalidates an old
exact archive; use its `case.json` with `--case` for a new run under updated tools.

```sh
python3 scripts/test-source-call-rust.py
python3 scripts/test-semantic-call-differential.py
python3 scripts/test-semantic-call-campaign.py
python3 Tests/scripts/test-semantic-call-corpus.py
python3 scripts/semantic-call-campaign.py \
  --corpus scripts/semantic-call-corpus.json \
  --output .upstream/semantic-call-ci --seconds 600
```

The external suite passed ten scenarios and 26 transactions, including nineteen
returns and seven root reverts, followed by exact archive replay. It covers all
eight prescribed modes, Word boundaries, value retained after child success,
both rollback levels, fresh private cells and aggregate branches. Six separate
identity sequences covering fifteen transactions also matched original Core and
imported Hull. Full repository build/tests and kernel policy passed, along with
eleven protocol and thirty campaign regressions.

The fixed manifest contains fourteen scenarios and 38 transactions, nineteen
step AST features, inputs zero through seven/maximum/high-bit, helper and
transaction counts one through three, and four generation templates. Coverage
distinguishes prescribed `input & 7` modes from observed root outcomes and
ordered committed log patterns. Neither is internal opcode trace coverage.
Native materialization, strict replay and repeated observations passed all
fourteen scenarios and 38 transactions, with complete declared coverage and
24 negative checks, including fuel exhaustion. This validator does not execute
the EVM. The actual fixed campaign also passed all fourteen scenarios and 38
prefixes, with complete coverage. A copied log-payload difference at `tx-1`
reduced three transactions to one through three accepted reductions in six
candidate executions. All actual reports matched; exact archive replay and
synthetic same-fingerprint replay passed. Fuel exhaustion remained inconclusive
with prior accounts retained and unknown logs. Both constructor receipts must
verify their exact linked runtime bytes; a fresh run and exact replay also
passed after that check was added.

M5 is complete within its documented profiles. The bounded-call domain is one installed parent and
one child, valid Word calldata, fixed initial balances and slots zero/one.
Gas/nonce equivalence, precompiles, arbitrary accounts and deeper calls remain
outside this profile.


## Compare generic selection

The `runtime-generics` profile uses a genuinely polymorphic source function
`sc_select<a>(flag, left, right)` at Word, `(word, word)` or `sum<word, word>`.
Each plan contains an independently checked aggregate step graph. The wrapper
computes `left = step(input)` and `right = step(input + 1)` in order before
selection. Odd input selects the left candidate; even input selects the right.
Pair candidates include the original or incremented input as their second
field, and the result sums both fields. Sum candidates use distinct
constructors, and the right branch adds one to its payload. Each selected
value therefore contributes to the returned ABI Word.

The original Core reference contains a monomorphic curried selector closure
and the complete applied step graph. It does not import Rust's specialized
program or computed result. The full program passes the Core checker; the
source emitter's meaning preservation remains unproved.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-generics --seed 1 --nodes 384 --cases 12 --attempts 256 \
  --output .upstream/semantic-generics
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-generic-corpus.json --seconds 600 \
  --output .upstream/semantic-generic-ci
python3 Tests/scripts/test-semantic-generic-corpus.py
```

Native commands are `generic-generate SEED NODES COUNT ATTEMPTS FUEL` and
`generic-emit PLAN.json INPUT [FUEL]`. A plan has schema
`solcore-lean.generic-plan.v1`, a canonical checked `stepProgram`, and `variant`
equal to `word`, `pair` or `sum`. The case contains both `genericPlan` and its
complete applied original Core `program`. `observe`, `replay` and `shrink` use
the same commands as earlier pure profiles. The 512-node limit includes all
selector and ABI-input reference syntax; the step alone cannot exhaust that
budget and then hide additional wrapper nodes.

Generated plans use the four boundary inputs zero, one, maximum Word and the
high bit. Both the step and full reference must return at least two distinct
boundary results. Imported and reduced constant computations remain valid.
Seeded provenance is regenerated; every saved program, source, type variant,
input and ABI is reconstructed. Reduction preserves the type variant, helper
count and typed binder inventory while strictly decreasing the complete
reference. A reduced case records its canonical parent plan and input; replay
checks the claimed decrease instead of trusting a `reduced` label.

The corpus's `genericRequirements.instantiations` contains the six combinations
`word:even`, `word:odd`, `pair:even`, `pair:odd`, `sum:even` and `sum:odd`.
`genericCoverage` records these prescribed combinations only after real
three-way agreement. They are not measured specialization or opcode coverage.
The step AST feature inventory and declared helper count exclude the selector
and ABI wrapper. Rejection, resource exhaustion and missing paths cannot meet
coverage requirements. The common campaign's archive replay, explicit synthetic
mismatch adapter and reduction checks apply unchanged.

The fixed corpus contains 28 cases across seven plans. All passed the actual
three-path comparison, covering nineteen step AST features, all four step
recipes, one through three helpers and every required variant/parity pair.
Native validation also checks twelve strictly smaller candidates and fifteen
negative cases. A separate generated pair case reduced its high-bit input to
zero in eight accepted candidate executions while preserving the synthetic
failure fingerprint and type. Original/reduced archive replay and synthetic
replay passed. A fuel-one run remained inconclusive. Capturing closures,
comptime and module combinations remain separate M6 slices.
