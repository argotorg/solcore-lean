# Generated semantic comparisons

The implementation plan and completion criteria are in
[Semantic differential testing milestones](../docs/design/semantic-differential-testing.md).
The reference Rust revision remains `2a745e12974c373c3799fec81b48a53c7dce2ab4`.

For pinned tool preparation, all-profile fixed and random suites, CI scheduling
and retained findings, see [Running the semantic test suite](SEMANTIC_CI.md).

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
For the closed G0, runtime-input, named-helper, raw-primitive, call-graph,
private-mutation, aggregate, aggregate call-graph and call-graph loop emitters, a kernel-checked theorem relates the emitted text to
the original Core result under an independent source semantics. It assumes Rust parsing, typing, compilation and execution; see
[scalar emitter meaning](../docs/design/scalar-emitter-meaning.md). Core typing
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
the original Core result, compiles checked Rust Hull and exact Sonatina
images, deploys those bytes on Anvil, and executes the same imported contract
through Core. Every passing run has three completed observations and three
matching pairwise comparisons. No saved expected result is trusted.

The default backend is `sonatina-o0`. Select `--backend sonatina-o2` to compile
the same source with the real O2 pipeline. Both choices use the pinned
Sonatina revision and its authoritative linker symbol extents. The pure,
storage and call adapters, their campaigns and `semantic-suite.py` accept the
same option. Run separate output directories for each backend; each has its
own observations, compilation failures and finding fingerprint.

For the fourteen pure profiles, `--backend yul --solc PATH` instead runs the checked
Rust Yul output through solc `0.8.35+commit.47b9dedd` with optimization and Osaka
enabled. The EVM deploys the creation bytes and checks its installed runtime
against the deployed bytes from the same solc compilation. Imported Hull uses
separately validated Sonatina O0 images, recorded explicitly in `pathBackends`.
This compares the same pure result without claiming Yul-linked Hull execution.
The stateful adapters reject Yul. No backend silently falls back to another.

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
and tool drift, restores the saved budgets and backend, and performs fresh
executions. An explicit conflicting backend is rejected. A legacy report with
no backend field denotes O0; invalid or null fields do not. Both artifact and
export provenance must agree with the selected optimization level.
Yul additionally retains and checks the exact compiler input/output, Yul source,
compiler identity and matching main/Yul Hull artifacts. Both original and
reduced module archives can be moved before replay; compiler settings and
recorded binary hashes remain fixed. `--solc` may identify the same executable
at another path, but cannot change its hash or full version during exact replay.
To deliberately change budgets, backend or tools, use the saved `case.json` with
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

## Compare the extended Word primitives

`runtime-primitives` retains the original checked Word-to-Word Core function
and imports raw functions from `std.opcodes`. It adds unsigned and signed
division/remainder, signed greater-than, shifts, byte selection, sign extension,
exponentiation, leading-zero count and modular addition/multiplication.
The [mapping table](../docs/design/next-implementation-roadmap.md#3-missing-runtime-operation-mappings)
records operand order and boundary behavior. Raw division/modular operations
return zero for a zero divisor/modulus; the public convenience wrappers are
not interchangeable with those raw functions.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-primitives \
  --backend sonatina-o0 --output .upstream/semantic-primitives-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-primitives \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-primitives-random
```

Repeat with `--backend sonatina-o2` or `--backend yul --solc PATH`. The fixed
manifest contains 81 hand-specified cases and requires all fourteen new AST
operators plus eight input boundaries. This is AST and observed result coverage,
not proof that an optimizer emitted or executed a particular opcode.

Generation uses the unchanged broad Core generator, then abstracts a literal
and requires varied completed results over 0, 1, 2, 255, 256, maximum Word, the
high bit and the high bit minus one. One accepted function produces up to eight
inputs in that order. Default generation uses a 96-node complete applied-program
budget and 512 attempts; the admitted range is 8–512 nodes. The new schema and
versions preserve earlier profile output. Imported boundary cases may be
constant. Typed shrinking can reduce both function bodies and inputs, and
strict replay rederives generation, source, ABI and the original Core result.

Native commands are `primitive-generate SEED NODES COUNT ATTEMPTS FUEL` and
`primitive-emit FUNCTION.json INPUT [FUEL]`; `replay`, `observe` and `shrink`
dispatch the new schema. Use `replay` to authenticate a saved case; `observe`
only executes its admitted Core program and does not authenticate saved source.

## Raw primitives in aggregate-based step functions

Eleven profiles render their checked aggregate step functions with
`AggregateRenderer`: `runtime-aggregates`, `runtime-loops`,
`runtime-generics`, `runtime-closures`, the step functions of
`runtime-comptime` and `runtime-modules`, and the five stateful profiles
(storage, rollback, parent/child calls, keyed storage and dynamic arrays).
Since emitter version 2 these step functions also render the fourteen raw
primitives: Clz, unsigned and signed division and remainder, signed
greater-than, the three shifts, byte selection, exponentiation, sign
extension, and the ternary `addmod`/`mulmod`. Previously every generated
program containing one of them was an operator exclusion.

The renderer uses the call-graph helpers exactly as the aggregate call-graph
renderer does. Each primitive operand is snapshotted into a fresh local in
Core evaluation order before the alias is called; shifts print
`shl(shift, value)` from those snapshots; signed comparison is converted with
`tobool`; ternary operands are all snapshotted. The original operations
(`+ - * & | ^ == > ! ~`) keep their exact unsnapshotted text, so every program
without a raw primitive emits byte-identical source. The aliases are imported
only when a rendered step uses one: profiles without another opcode import add
the primitive profile's `import { div as sc_div, ... } from std.opcodes;`, and
the stateful profiles append the same aliases to their existing `std.opcodes`
import. Pair, sum, case and private-cell scoping are unchanged.

Every affected emitter version and profile version moved to `v2`, including the
shared aggregate step profile version, because accepted programs changed. Saved
cases of the older versions are rejected by the explicit version check rather
than re-emitted: all 202 legacy cases of the six affected pure profiles fail
with `profileVersion changed`, while all 347 legacy cases of the other eight
pure profiles replay to identical JSON.

Out of scope and unchanged: `ScalarRenderer`, which the priority-5 emitter
proof unfolds, and its users (`closed-g0`, `runtime-word`, `runtime-functions`
and the compile-time constants of `runtime-comptime` and `runtime-modules`);
`MutationRenderer` (`runtime-mutation`, 22 operator exclusions in the recorded
random allocation); and the exclusions for node budgets too small for an
aggregate template.

Operator exclusions for root seed `20261026`, sixteen cases and 2,048 attempts
(the recorded random suite allocation, generation only):

| Profile | Before | After | Attempts before → after |
| --- | ---: | ---: | --- |
| runtime-aggregates | 42 | 0 | 46 → 4 |
| runtime-loops | 23 | 0 | 26 → 3 |
| runtime-generics | 33 | 0 | 37 → 4 |
| runtime-closures | 47 | 0 | 51 → 4 |
| runtime-comptime | 376 | 17 (constants) | 382 → 32 |
| runtime-modules | 574 | 9 (constants) | 636 → 18 |
| stateful-storage | 206 | 0 | 222 → 16 |
| stateful-storage-rollback | 206 | 0 | 222 → 16 |
| stateful-calls | 149 | 0 | 180 → 18 |
| stateful-keyed-storage | 180 | 0 | 196 → 16 |
| stateful-dynamic-array | 163 | 0 | 195 → 17 |

The remaining comptime and module operator exclusions come only from their
`ScalarRenderer` constants. Template-budget exclusions are unchanged in kind
(1 for modules, 2 for calls and 1 for dynamic arrays in this allocation).

Each affected fixed corpus gained generated entries whose step functions cover
all fourteen primitive AST features, and requires them: two or three seeds per
profile at every boundary input for the pure profiles, and two or three
scenarios for the stateful ones. Expected keyed and dynamic-array histories were
computed by an independent Python evaluator with the documented EVM primitive
semantics and matched original Core. The native corpus validators now admit
primitive step features (constants still admit only the original scalar set)
and count ternary nodes like `if` nodes, as the Wire measure does.

| Corpus | v1 cases | v2 cases |
| --- | ---: | ---: |
| aggregates | 32 | 44 |
| loops | 48 | 60 |
| generics | 28 | 36 |
| closures | 24 | 32 |
| comptime | 32 | 40 |
| modules | 32 | 44 |
| storage | 10 | 12 |
| storage rollback | 12 | 14 |
| calls | 14 | 16 |
| keyed storage | 12 | 14 |
| dynamic arrays | 12 | 15 |

Local validation ran on commit `660a2729b` with frozen scripts and native
tools; all 1,358 per-case reports record that commit and a clean tracked tree.
The fixed suites matched all 256 pure cases on O0, O2 and Yul (1,429.9, 1,441.0
and 2,324.3 seconds) and all 71 stateful scenarios and 197 transaction prefixes
on O0 and O2 (416.4 and 423.1 seconds), with complete coverage including every
primitive feature. The random suites (root seed `20261026`, sixteen cases and
2,048 attempts per profile) matched all 96 pure cases on O0, O2 and Yul (556.2,
557.8 and 863.9 seconds) and all 80 stateful scenarios and 240 prefixes on O0
(485.6 seconds); 92 of the 96 accepted pure cases and 73 of the 80 stateful
scenarios call at least one alias. The O2 stateful random suite failed:
storage, rollback, calls and keyed storage matched 16 of 16 each, but dynamic
arrays matched fifteen and one scenario crashed O2 code-image export with the
panic recorded as Q013 (`Integer overflow when casting to usize`). The same
scenario matched on O0. Automatic reduction kept the crash fingerprint through
thirteen accepted candidates before its attempt limit; the reduced case still
shifts left by a large constant count. The crash is retained as a finding and
was neither suppressed nor reclassified, so that O2 gate did not pass.

## Compare directly generated call graphs

`runtime-call-graphs` generates typed Word/Bool expressions with the runtime
parameter already in scope. One to three helpers can call any earlier helper;
the entry and arguments need not follow a fixed chain. Local bindings,
conditionals and all scalar primitives are admitted. The original Core checker
seals the complete graph, and the original Core application supplies the oracle.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-call-graphs \
  --backend sonatina-o0 --output .upstream/semantic-call-graphs-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-call-graphs \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-call-graphs-random
```

O2 and Yul use the same cases with their usual backend flags. The fixed corpus
contains 56 cases with hand-specified Core results. It requires helper counts
one through three, eight input boundaries and nine syntactic structures:
skipped helpers, multiple callees, shared callees, nested calls, calls in
branches and local bindings, a diamond, calls in predicates and primitive
operands. `callShapeCoverage` records required, generated, matched and missing
structures. Only completed matches satisfy coverage. The inventory includes
all declared bodies; it does not claim an executed call trace or branch coverage.

The default complete-program budget is 192 nodes, with 1,024 generation
attempts. Explicit attempt limits override this default. The admitted budget
range is 13–512 nodes; small budgets can exhaust generation because a generated
entry must contain a call. Generated functions must also return varying values
over the same eight inputs used by `runtime-primitives`. Imported functions
may be constant. Attempts count graphs, while cases count individual inputs.

`call-graph-generate SEED NODES COUNT ATTEMPTS FUEL` and
`call-graph-emit FUNCTION.json INPUT [FUEL]` produce the new case schema.
Replay regenerates the original graph and body budgets, checks canonical
source, input, versions and structural metadata, and recomputes Core results.
Reduction retains the helper bindings, reseals every candidate and requires a
strictly smaller complete application. Its failure identity and selected
backend follow the ordinary campaign rules. The older chain-based profile
below keeps its existing schema and generator unchanged.

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
graph. Fixed seeds use individual budgets within that limit. Since emitter
version 2 the raw primitives render as described in
[Raw primitives in aggregate-based step functions](#raw-primitives-in-aggregate-based-step-functions);
integer operations remain explicit exclusions.

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

## Compare bounded loops over call graphs

`runtime-call-graph-loops` uses a directly generated scalar call graph as the
step of the bounded loop above. Its unchanged helpers and arbitrary entry are
resealed by the aggregate DAG checker and then by the existing bounded-loop
plan; the executed step program is the scalar graph's exact declaration chain.
The finite ordinal-guard Core reference and its typing are reused, with no new
evaluator or Core primitive. The source emits the helpers, then the entry as
`sc_step`, with the call-graph renderer and raw `std.opcodes` aliases, inside
the same `while (limit > counter)` wrapper. The older `runtime-loops` emitter
and its narrower renderer are unchanged. The ABI is
`SynthesizedCallGraphLoops.run(uint256)`.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-call-graph-loops \
  --backend sonatina-o0 --output .upstream/semantic-call-graph-loops-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-call-graph-loops \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-call-graph-loops-random
```

A plan has schema `solcore-lean.call-graph-loop-plan.v1`, a scalar
`stepProgram` and a `mask` of zero, one, three or seven. Generation first draws
mask one, three or seven, subtracts that mask's measured wrapper overhead from
the complete applied-program budget, generates the step with the
`runtime-call-graphs` grammar and remeasures the complete loop. The default
budget is 256 nodes; the admitted range is 39–512, and the mask-seven wrapper
alone needs 111. An accepted plan needs an entry call, step results that vary
over the eight primitive inputs and a positive-trip loop input whose final
value differs from that input. Imported and reduced plans may be constant or
use mask zero. Each plan yields up to six inputs: zero, one, three, seven,
maximum Word and the high bit. Attempts count plans; cases count inputs.

`call-graph-loop-generate SEED NODES COUNT ATTEMPTS FUEL` and
`call-graph-loop-emit PLAN.json INPUT [FUEL]` produce the case schema
`solcore-lean.semantic-call-graph-loop-case.v1`. Every origin rebuilds the
canonical applied reference from the saved plan. Replay regenerates generated
plans with their step origin and budget, and checks canonical source, ABI,
versions, features, helper count and call shapes. Reduction retains helper
bindings, reseals each candidate as a plan, never raises the mask and requires
a strictly smaller complete application; smaller masks remove whole guards.
A reduced origin names its parent plan and input.

The fixed corpus has eight imported and three generated plans at all six inputs.
Its expected Words were computed outside Lean from EVM Word semantics and the
loop definition; the native corpus test checks each against original Core.
It requires all thirty scalar AST features including calls, one to three
helpers, the nine call shapes, and masks and iterations zero, one, three and
seven. `loopCoverage` and `callShapeCoverage` count only three-way matches.
Neither inventory is an executed trace, call path or opcode measurement.

Native validation confirmed all 66 expected Words and replayed 264 strictly
smaller typed reductions. All 66 fixed cases matched on O0, O2 and Yul; the
first O2 run had stopped on one host adapter error before any execution, and a
fresh run matched all 66. That error was macOS rejecting `killpg` with `EPERM`
for a group holding only an exited, unreaped member; process cleanup now
tolerates it. Random seed `20261026` with sixteen cases and 2,048
attempts matched all sixteen on each backend. A controlled synthetic reduction
accepted four typed reductions per backend, all keeping three helpers, and
original and reduced archives replayed exactly.

## Compare aggregate compositions with call graphs

`runtime-aggregate-call-graphs` generates typed Word, Bool, Word-pair and
Word-sum expressions directly, with the runtime parameter in scope. One to
three helpers may call any earlier helper. Pairs, sums, projections, let-bound
aggregates, aggregate-valued branches and case expressions compose with those
calls in operands, components, payloads, scrutinees and branches. Helper
arguments and results and the ABI remain Words. Private cells and Unit values,
covered by `runtime-aggregates`, are outside this grammar. The existing
aggregate DAG checker seals each graph; original Core supplies the oracle.

```sh
python3 scripts/semantic-suite.py --mode fixed --profile runtime-aggregate-call-graphs \
  --backend sonatina-o0 --output .upstream/semantic-aggregate-call-graphs-fixed
python3 scripts/semantic-suite.py --mode random --profile runtime-aggregate-call-graphs \
  --seed 20261026 --cases 16 --attempts 2048 \
  --output .upstream/semantic-aggregate-call-graphs-random
```

Source uses the call-graph renderer's scalar, raw-primitive, snapshot and call
formatting, and the aggregate profile's tuple, `sum<word, word>`, `inl`/`inr`
and `match` forms; a test checks scalar bodies render identically to the
call-graph profile. The default budget is 192 complete-program nodes, admitted
13–512. Accepted graphs need an entry call, a call composed with an aggregate
value or payload scope, and varied results over the eight primitive inputs.
Imported graphs may be constant. Each graph yields up to eight inputs.

`aggregate-call-graph-generate SEED NODES COUNT ATTEMPTS FUEL` and
`aggregate-call-graph-emit FUNCTION.json INPUT [FUEL]` produce the case schema
`solcore-lean.semantic-aggregate-call-graph-case.v1`. Replay regenerates the
graph and budgets and checks canonical source, ABI, versions, features, helper
count and composition shapes. Reduction reuses the typed aggregate reductions:
every helper, typed let and case payload scope is retained, candidates stay in
this grammar and must strictly decrease the complete application.

`aggregateShapeCoverage` records nine syntactic structures: calls in pair
components and sum payloads, calls on projections, calls in case scrutinees and
branches, calls on a case payload, let-bound aggregates, aggregate-valued
branches and nested cases. Only completed matches satisfy coverage; this does
not claim that a call, branch or payload executed. The fixed corpus has four
imported and three generated graphs at all eight inputs. Its expected Words
were computed outside Lean, and native validation checks each against original
Core. It requires all 36 scalar and aggregate AST features, one to three helpers
and the nine structures.

Native validation confirmed all 56 expected Words and replayed 224 strictly
smaller typed reductions. All 56 fixed cases matched on O0, O2 and Yul. Random
seed `20261026` with sixteen cases and 2,048 attempts matched all sixteen on O0
and Yul; O2 matched eight and retained eight compiler crashes from one graph,
a recorded upstream finding, so that O2 random run fails. A controlled
synthetic reduction accepted four typed reductions per backend, keeping every
helper and binder, and original and reduced archives replayed exactly.

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
linked Sonatina images at the selected O0/O2 level, verifies the deployed runtime bytes, and sends actual
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

## Compare keyed storage transactions

The `stateful-keyed-storage` profile is the first state/ABI extension. Each
transaction calls `SynthesizedKeyedStorage.run(uint256 key, uint256 input)`,
selector `0x7357f5d2`, with exactly two ABI Words. The key selects an arbitrary
full-width slot. The contract reads `old = sload(key)` and the counter
`count = sload(0)`, computes `step(input + old)` with the checked aggregate
step, then writes, in this order:

| Order | Slot | Value |
| --- | --- | --- |
| 1 | `key` | the step result |
| 2 | `key + 1`, wrapping | `old` |
| 3 | `0` (counter) | `count + 1` |

It rereads all three slots and returns their wrapped sum. An odd input reverts
after those writes and rereads, with the same Word as a 32-byte payload, so the
committed world keeps its predecessor. Later writes win when slots alias: key
zero is the counter, key maximum's successor wraps to the counter, and a
transaction may read another transaction's key or successor slot. The original
Core contract uses `wordOutcomeV1`; `ContractRuntime` commits or rolls back.

Observations are declared by the case, not discovered from one path.
`observedSlots` is the sorted, duplicate-free set containing the counter and
every transaction's key and wrapping successor. All three paths report status,
payload and the committed value of every declared slot after every transaction.
Original Core reads them from the public committed world; the Rust EVM path
uses `eth_getStorageAt` at each receipt block; imported Hull reads its committed
entries. Because Core's account storage is not enumerable, slots outside the
declaration are checked only on the two executable paths: the Hull runner
reports every nonzero committed slot outside it, and the EVM path asks Anvil's
`prestateTracer` in diff mode for each mined transaction's (and the
deployment's) changed slots, then rereads those outside the declaration at the
receipt block. A nonzero undeclared slot on either path is a semantic mismatch
(`undeclaredStorage`, with `undeclaredPaths`). A diff that changes another
account's storage fails closed as an adapter error. The deployment must leave
every declared slot zero and no undeclared nonzero slot.

Build the native tools and generate a case:

```sh
lake build semanticKeyedStorageTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-keyed-storage-cases
.lake/build/bin/semantic-keyed-storage-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-keyed-storage-cases/corpus.json
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the two-slot tools. Plans use `solcore-lean.keyed-storage-plan.v1`
under the case field `keyedStoragePlan`; cases use
`solcore-lean.semantic-keyed-storage-case.v1`. Transactions are
`{id, key, input, calldata, value}` with canonical decimal Words, the selector
followed by both Words, and zero value. Bindings reuse
`solcore-lean.storage-bindings.v1`. Existing storage, rollback and call schemas,
plans and saved cases are unchanged.

Generation reuses the aggregate step generator, so most attempts are ordinary
exclusions of operators the source renderer does not admit; 207 of the first
3,000 seeds at the default 384-node budget were accepted.
Three transactions draw keys from a six-entry bank (zero, one, the high bit, a
full-width pattern, maximum minus one and maximum), inputs from the six storage
boundaries adjusted to a prescribed parity, and one of four completion patterns
(all return, or one revert in the first, second or third position). These
choices use the high halves of draws from a separate stream, so they do not
correlate with the step seed's helper and template digits. Generated scenarios
must complete with exactly the prescribed outcomes under original Core.
Imported and reduced scenarios may use any one to three transactions.

Reduction simplifies the checked step (keeping every helper and binder),
removes transactions while keeping stable IDs, and replaces one input or key by
a bank value. The order is transaction count, complete program complexity, then
the sum of all keys and inputs. Every candidate rederives its observed slots,
so a reduction that drops the slot of a finding cannot preserve that finding.

```sh
python3 scripts/semantic-storage-differential.py \
  --case .upstream/semantic-keyed-storage-cases/case.json \
  --output .upstream/semantic-keyed-storage-cases/run
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-keyed-storage-corpus.json \
  --output .upstream/semantic-keyed-storage-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-keyed-storage \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-keyed-random
```

The storage runner and campaign select the keyed native tool, Hull runner and
comparison rules from the case or manifest profile. `--backend sonatina-o2`
works as for the other storage profiles; Yul is rejected. The synthetic
adapter accepts `--test-field storage:SLOT` for any declared decimal slot of
the original scenario; a candidate that no longer declares that slot is an
ordinary, non-preserving analysis. Fingerprints name differing slots and, for
this profile, the paths with undeclared storage.

The fixed corpus has twelve scenarios and 33 transactions: eight imported plans
and four generated seeds. Its expected histories were computed outside Lean by
a separate evaluator of the step programs and a direct model of the protocol;
`Tests/Main.lean` registers a validator that compares every status, payload
and declared committed slot with original Core and rejects tampered entries.
Required coverage is all 21 step AST features in the corpus, the six inputs,
the six bank keys, one to three helpers and transactions, all four generator
templates, both outcomes, six completion patterns and four static alias kinds:
`key-counter`, `successor-counter`, `repeated-key` and `successor-key`. Alias
kinds describe the transaction keys; they do not claim an aliasing write was
committed or that a particular opcode was executed.

Local validation used committed code with frozen scripts and native tools.
The fixed suite matched all twelve scenarios and 33 transaction prefixes on
Sonatina O0 and O2, with complete coverage, in 69.7 and 69.6 seconds. The
recorded random suite (root seed `20261026`, sixteen cases, 2,048 attempts)
accepted sixteen scenarios from 196 attempts, with 180 ordinary generation
exclusions and no resource exclusions. All sixteen scenarios and 48 prefixes
matched on both levels in 92.5 and 92.4 seconds; they covered all four
completion patterns and alias kinds. Neither run produced a finding.

A copied `importedHull` difference in slot one at `tx-1` of the counter-alias
corpus scenario was reduced on each level to that one transaction with key and
input zero: four accepted reductions in five candidate executions, all of whose
actual comparisons matched. The original and reduced archives replayed exactly
with three-way agreement (four replays), and fresh synthetic replays reproduced
the same fingerprint. Core or Hull fuel one was classified as inconclusive. The
two existing storage profiles still matched all 22 fixed scenarios and 60
prefixes on each level with the extended adapter, and the eight existing native
tools kept their hashes. Changing the shared adapter does invalidate exact
replay of earlier storage archives, as for any adapter change.

This profile does not compare gas, balances, nonces, logs or code, nor
malformed calldata, Solidity-style hashed mapping layouts, dynamic ABI values,
multiple callers or nonzero call value. Undeclared-slot containment is checked
on the Hull and EVM paths only. Agreement in these runs is test evidence, not
a preservation proof. After the adapter was generalized for dynamic arrays
below, the keyed fixed and random suites were repeated on both levels with the
same results.

## Compare bounded dynamic arrays

The `stateful-dynamic-array` profile adds one bounded dynamic ABI value. Each
transaction calls `SynthesizedDynamicArray.run(uint256 flags, uint256[] values)`,
selector `0x9a94c44b`, with zero to three elements in the canonical head/tail
encoding: flags, the tail offset 64 relative to the arguments, the length and
the elements. The source parameter is a lazily decoded
`calldata<array<uint256>>`; it reads `values.length()` and `values[uint256(i)]`.
Original Core follows the head offset to the same length word and element Words
with `inputDataWordBE?`, as the ABI does.

The contract reads the accumulator from slot 0. For each present element `i`
(at most three, unrolled in both Core and source) it computes
`acc = step(acc + values[i])` and writes slot `1 + i`. It then writes the
accumulator to slot 0, adds the length to a running element count in slot 4,
and returns the sum of slots 0 and 4. Odd flags revert after those writes with
the same Word. Shorter arrays leave earlier per-element slots untouched, and an
empty array still rewrites the accumulator and count. Observed slots are fixed
at zero through four, and the keyed profile's containment rules apply: the
Hull and EVM paths must show no nonzero committed slot outside them. The
declared-slot Hull runner `rust-hull-keyed-storage-scenario` serves both
profiles because it accepts the declared slots and calldata from the scenario.

```sh
lake build semanticDynamicArrayTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-dynamic-array-cases
.lake/build/bin/semantic-dynamic-array-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-dynamic-array-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-dynamic-array-corpus.json \
  --output .upstream/semantic-dynamic-array-ci --seconds 900
```

Plans use `solcore-lean.dynamic-array-plan.v1` under `dynamicArrayPlan`; cases
use `solcore-lean.semantic-dynamic-array-case.v1`. Transactions are
`{id, flags, values, calldata, value}`; the tool and the adapter both reject
calldata that is not the canonical encoding of the saved flags and values,
arrays longer than three elements and noncanonical Words. The calldata of twelve
generated transactions, including empty arrays, matched `cast calldata` from the
pinned Foundry release byte for byte; the Lean tests retain two such vectors.
Non-canonical
offsets, truncated arrays and the Rust decoder's revert paths are outside this
profile: Core reads an absent Word as zero, while the Rust ABI decoder reverts.

Generation reuses the aggregate step generator; 235 of the first 3,000 seeds at
the 384-node default were accepted. Three transactions draw lengths zero to
three, elements and flags from the six storage boundary inputs, and one of the
four completion patterns from a separate high-bit stream. Reductions simplify
the step, remove a transaction, remove one array element, or replace one
element or the flags by a bank value. They are ordered by transaction count,
program complexity, total element count, then the sum of flags and elements.
The campaign records array lengths as a coverage dimension and treats every
element as a runtime input.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions with independently computed histories, validated against original
Core by a registered Lean test. It requires all 23 step AST features of the
corpus, the six boundary elements, lengths zero through three, one to three
helpers and transactions, all four templates, both outcomes and six completion
patterns.

Local validation used committed code with frozen scripts and native tools. The
fixed suite matched all twelve scenarios and 33 prefixes on Sonatina O0 and O2
with complete coverage, in 94.7 and 94.1 seconds. The recorded random suite
(root seed `20261026`, sixteen cases, 2,048 attempts) accepted sixteen
scenarios from 195 attempts, with 179 ordinary exclusions and no resource
exclusions; all sixteen and 48 prefixes matched on both levels in 109.8 and
108.4 seconds, covering every length and all four generated completion
patterns. Neither run produced a finding. A copied `importedHull` difference in
slot three at `tx-0` of a three-transaction scenario was reduced on each level
to that transaction with an empty array: six accepted reductions in eight
candidate executions, all of whose actual comparisons matched. The original and
reduced archives replayed exactly with three-way agreement (four replays), and
synthetic replays reproduced the fingerprint. Core or Hull fuel one was
inconclusive. The keyed, two-slot storage and rollback fixed corpora still
matched on both levels with the generalized adapter.

This profile compares one dynamic Word array beside one static Word. Nested or
multi-word element types, `bytes` and strings, ABI-encoded return values and
dynamic memory are outside it, as are gas, balances, nonces and logs. Agreement
is test evidence, not a preservation proof.

## Compare committed event logs

The `stateful-logs` profile makes event logs committed observations. Each
transaction calls `SynthesizedLogs.run(uint256 flags, uint256 input)`,
selector `0x7357f5d2`, with exactly two ABI Words. A plan holds the checked
aggregate step and zero to three log sites. A site has a guard bit `g` (one,
two or three, strictly increasing across sites), a topic count `n` from zero
to four and a data length of zero, one or two Words.

The contract reads `old = sload(0)` and `count = sload(1)`, computes
`result = step(input + old)`, then writes `result` to slot 0 and `count + 1`
to slot 1. Each site in order whose guard bit is set in `flags` computes
`value = step(result + g)` and emits one LOGn record:

| Field | Value |
| --- | --- |
| Emitter | the contract address |
| Topics | `value + 1`, ..., `value + n` |
| Data | `value`, then `result`, as big-endian Words; first `w` of them |

The source emits it with the pinned `std.opcodes` wrapper `log0` to `log4`
over a buffer reserved from the free-memory pointer. Odd flags then revert
with `result` as a 32-byte payload; otherwise `run` returns `result`.

### Definitions

These definitions were fixed before any execution.

- **Log observation.** For each transaction, the ordered list of committed
  logs `{address, topics, data}`: the emitter as a decimal address, zero to
  four decimal topic Words and the data as hexadecimal bytes. The Rust EVM
  path reads the `logs` of each mined receipt in log-index order. Imported
  Hull reads the logs of each actual receipt from the declared-slot runner.
  Original Core's host interface has a single log primitive,
  `emitLogWord(topic, payload)`, with one topic Word and one data Word. The
  Core contract therefore writes each site as a frame of `1 + w + n` word
  logs, and the observer decodes the committed journal of the public
  top-level runtime under framing `core-word-log-framing-v1`:

  | Record | Topic Word | Payload Word |
  | --- | --- | --- |
  | Header | `256 + 16 * w + n` | `0` |
  | Data `i`, for `i` = 1..`w` | `512 + i` | data Word `i` |
  | Topic `j`, for `j` = 1..`n` | `768 + j` | topic `j` |

  Every record of a frame must come from the same emitter. A journal that is
  not a sequence of complete frames is an observer failure, never an empty or
  partial log list. The framing is a convention of this profile, not a Core
  LOGn semantics; Core and its host interface are unchanged.
- **Rollback.** A reverted transaction has no committed logs on any path and
  keeps the prior committed slots. Original Core's public runtime selects the
  checkpoint journal and world; Hull receipts of failed calls export no logs;
  EVM receipts of failed transactions carry none. Logs committed by earlier
  transactions stay committed: after the sequence, `eth_getLogs` over the
  whole local chain for the contract must return exactly the concatenation of
  the deployment and per-transaction receipt logs. The Core and Hull histories
  report each transaction's committed logs once and never retract them. An
  out-of-fuel or otherwise incomplete transaction has unknown logs (`null`)
  and ends the sequence.
- **Deployment.** The contract has no constructor and emits no constructor
  logs. The Hull and EVM deployment receipts must contain no logs and leave
  slots 0 and 1 zero, with no nonzero undeclared slot. Original Core starts
  from the declared post-deployment world with no logs. A deployment log on
  any path is a semantic mismatch at the initial stage.
- **Committed comparison.** After every transaction all three paths must agree
  on status, payload, slots 0 and 1, and the ordered committed logs. The keyed
  profile's containment rules apply to slots outside 0 and 1 on the Hull and
  EVM paths. Each path's logs must also have the static shape that the plan
  and flags determine: on return, one log per guarded site, in site order,
  from the contract address, with that site's topic count and 32 times its
  data length bytes of data; on revert, none.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, remove one log
  site (the others keep their guards) or drop its last topic or last data
  Word, replace one transaction's input by a storage boundary input, clear
  one of bits zero to three of its flags, or keep only those four bits. They
  are ordered by transaction count, complete program complexity, then the sum
  of all flags and inputs. A candidate that no longer emits the log of a
  finding cannot preserve that finding.

Coverage adds four dimensions to the storage step dimensions: committed log
counts per transaction, committed topic arities, committed data lengths in
bytes, and the number of guarded sites of each reverted transaction, whose
logs rollback must discard. Generated coverage derives them from the plan and
flags; matched coverage uses the actual original-Core histories.

### Running and validation

```sh
lake build semanticEventLogTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-log-cases
.lake/build/bin/semantic-log-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-log-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-log-corpus.json \
  --output .upstream/semantic-log-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-logs \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-log-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.log-plan.v1`
under the case field `logPlan`, with the step program and its `sites`; cases
use `solcore-lean.semantic-log-case.v1` and record `framingVersion` in their
provenance. Transactions are `{id, flags, input, calldata, value}`.
Histories use `solcore-lean.log-history.v1`: the storage history fields plus
`initialLogs`, the per-transaction `logs` (`null` when unknown) and, on the
EVM path only, `chainLogs`. The declared-slot Hull runner
`rust-hull-keyed-storage-scenario` already exported every receipt's logs, so
it serves this profile unchanged. The storage runner and campaign select the
native tool and comparison rules from the case or manifest profile.
`--backend sonatina-o2` works as for the other storage profiles; Yul is
rejected.

Generation measures the wrapper of the chosen sites and gives the remaining
node budget to the aggregate step generator. A separate high-bit stream
chooses one to three sites (guards, topic counts and data lengths), three
boundary inputs, the guard bits of each transaction's flags, whether its flags
also set the high bits `2^255 + 16`, and one of the four completion patterns.
Of the first 300 seeds at the 384-node default, 283 were accepted; the others
left too few nodes for the selected step template. Generated scenarios must
complete with the prescribed outcomes, and their decoded logs must have the
static site shapes under original Core.

The synthetic adapter accepts `--test-field log`: it flips the low bit of the
first committed log's first topic, or of its last data byte when it has no
topic, in a copied history. A transaction without such a log cannot carry the
synthetic finding. Fingerprints name `logPaths` for deployment and chain-log
differences.

The fixed corpus has twelve scenarios and 33 transactions that commit 27 logs:
eight imported plans, which reuse the dynamic-array corpus steps with new site
layouts and flags, and four generated seeds. Its expected histories, including
every topic and data byte, were computed outside Lean by a separate evaluator
of the step programs and a direct model of the protocol. `Tests/Main.lean`
registers a validator that compares every status, payload, slot and log with
original Core and rejects tampered topics, data, emitters and log order.
Required coverage is all 39 step AST features in the corpus, the six inputs,
one to three helpers and transactions, all four templates, both outcomes, six
completion patterns, committed log counts zero to three, topic arities zero to
four, data lengths of 0, 32 and 64 bytes, and reverted transactions with zero
to three guarded sites.

Local validation used committed code with frozen scripts and native tools; the
eleven existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete coverage,
in 68.3 and 68.1 seconds. The recorded random suite (root seed `20261026`,
sixteen cases, 2,048 attempts) accepted sixteen scenarios from eighteen
attempts, with two ordinary exclusions and no resource exclusions. Its 37 sites
took all fifteen combinations of topic count and data length. O0 matched all
sixteen scenarios and 48 prefixes in 92.7 seconds, committing 49 logs on each
path and covering every log count, topic arity and data length, four
completion patterns and discarded counts zero to two.

The O2 random gate failed. Fifteen scenarios and 45 prefixes matched; scenario
`generated-14` (seed `11810673490881475037`) crashed the compiler during O2
code-image export with a host `arithmetic operation overflow` panic in
`primitive-types`. Checked Hull export succeeded, and the same scenario matched
on O0. The panic message differs from the earlier `Integer overflow when
casting to usize` shift-count crashes. Automatic reduction accepted three of
sixteen candidates before its attempt limit and kept the crash fingerprint;
the reduced step's only remaining raw opcode call is `signextend` with index
31. The finding is retained, and the symptom is recorded without upstream
investigation.

A copied `importedHull` log difference at `tx-2` of the three-site,
three-transaction `identity-full-frames` scenario was reduced on each level to
that transaction with flags 2, input zero and one site with one data Word and
no topic: twelve accepted reductions in 28 candidate executions, all of whose
actual comparisons matched. The original and reduced archives replayed exactly
with three-way agreement (four replays), and synthetic replays reproduced the
fingerprint. Core or Hull fuel one was classified as inconclusive. With the
extended adapter, the two-slot storage, rollback, call, keyed and
dynamic-array fixed corpora still matched all 71 scenarios and 197 prefixes on
each level. Changing the shared adapter invalidates exact replay of earlier
storage archives, as for any adapter change.

This profile does not compare gas, balances, nonces or code, `LOG` from
constructors or from more than one contract, memory-dependent data lengths
other than whole Words, or ABI event signatures and indexing. Agreement is
test evidence, not a preservation proof.

## Compare nonzero call value

The `stateful-call-value` profile sends value with each transaction and makes
the contract's own balance a committed observation. Each transaction calls the
payable `SynthesizedCallValue.run(uint256 flags, uint256 input)`, selector
`0x7357f5d2`, with exactly two ABI Words and a call value from a fixed bank:
0, 1, 7, 2^64 - 1, 2^64 and 2^70. The source reads the value with the pinned
`std.opcodes` `callvalue` wrapper; original Core reads it with the
`callValue` host function.

The contract reads `old = sload(0)` and `total = sload(1)`, computes
`result = step(input + value + old)` with the checked aggregate step, writes
`result` to slot 0 and `total + value` to slot 1, then reverts with `result`
as a 32-byte payload if `flags` is odd and returns it otherwise. Slot 1 is the
committed value the contract has accepted, so after every committed
transaction the balance must equal the deployment value plus slot 1.

### Definitions

These definitions were fixed before any execution.

- **Value observation.** After deployment and after every transaction, all
  three paths report status, payload, slots 0 and 1, and the contract's
  committed balance as a decimal Word. The keyed profile's containment rules
  apply to other slots on the Hull and EVM paths. The sender's balance is
  never observed: on the EVM path it also pays gas. Original Core reads the
  contract account's balance in the committed world of
  `BalancedTopLevelExecution`, which transfers the call value from the caller
  to the contract before the root runs. The imported-Hull runner performs the
  same top-level transfer in its checked ledger, as the call runner does for
  its funded constructor, passes the value and entry balance to the Hull
  context, and commits the receipt ledger only on return. The EVM path reads
  `eth_getBalance` at each receipt block.
- **Funds.** A scenario sends at most 2^72 in total. The local Anvil sender
  holds its default funds; original Core and imported Hull fund the caller
  with 2^80. A transfer that original Core or Hull rejects is an execution
  error, never a revert.
- **Rollback.** A reverted transaction refunds its value: the contract keeps
  its prior committed balance and slots on every path. Original Core's
  balanced root runs on the post-transfer world with the pre-transfer world as
  its checkpoint; Hull keeps its prior ledger; the EVM reverts the transfer.
  An out-of-fuel or otherwise incomplete transaction has an unknown balance
  and ends the sequence.
- **Deployment.** The contract has an empty payable constructor and is
  deployed with a value of 0 or 5 recorded in the case. Every path starts with
  that balance, zero slots, no constructor logs and, on Hull and EVM, no
  nonzero undeclared slot. Original Core starts from the declared
  post-deployment world: the contract holds the deployment value and the
  caller 2^80.
- **Committed comparison.** After every transaction all three paths must agree
  on status, payload, slots 0 and 1 and the committed balance. Each path must
  also follow the fixed protocol: the flags parity selects the completion, the
  payload is one Word, a revert keeps the prior slots and balance, and every
  committed balance equals the deployment value plus slot 1.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, replace one
  input by a storage boundary input or one value by a smaller bank value,
  reduce one transaction's flags to their parity or clear its revert bit, or
  lower the deployment value to zero. They are ordered by transaction count,
  complete program complexity, then the sum of all flags, inputs and values
  and the deployment value.

Coverage adds three dimensions to the storage step dimensions: the call
values, the values of reverted transactions, whose refunds rollback must
perform, and the deployment values.

### Running and validation

```sh
lake build semanticCallValueTool rustHullValueScenario
mkdir -p .upstream/semantic-call-value-cases
.lake/build/bin/semantic-call-value-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-call-value-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-call-value-corpus.json \
  --output .upstream/semantic-call-value-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-call-value \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-call-value-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.call-value-plan.v1`
under the case field `callValuePlan`, with the step program and the
`deploymentValue`; cases use `solcore-lean.semantic-call-value-case.v1`.
Transactions are `{id, flags, input, value, calldata}`, where `value` is the
call value. Histories use `solcore-lean.call-value-history.v1`: the storage
history fields plus `initialBalance`, the per-transaction `committedBalance`,
`finalBalance` and the deployment `initialLogs`. The keyed-storage runner
rejects nonzero value, so the new runner `rust-hull-value-scenario` accepts
`callerFunds`, a constructor value and per-call values in its
`solcore-lean.value-contract-scenario.v1` scenarios and reports a rejected
transfer as `transfer-rejected`. Every value is at most 2^70, so a scenario of
at most four values, including the deployment value, sends at most 2^72.

Generation uses a separate high-bit stream for three boundary inputs, three
bank values, the deployment value and one of the four completion patterns;
flags are just the parity. All of the first 300 seeds at the 384-node default
were accepted. Generated scenarios must complete with the prescribed outcomes,
and their committed balances must equal the deployment value plus slot 1 under
original Core. The campaign's candidate identity includes the deployment value,
so a candidate that only lowers it is executed rather than skipped.

The synthetic adapter accepts `--test-field balance`: it flips the low bit of
the selected transaction's committed balance in a copied history.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new values, flags and
deployment values, and four generated seeds. Its expected histories, including
every committed balance, were computed outside Lean by a separate evaluator of
the step programs and a direct model of the protocol. `Tests/Main.lean`
registers a validator that compares every status, payload, slot and balance
with original Core and rejects tampered balances, values, deployment values and
committed refunds. Required coverage is all 39 step AST features in the
corpus, the six inputs, one to three helpers and transactions, all four
templates, both outcomes, six completion patterns, all six bank values, refunds
of 0, 1, 2^64 and 2^70, and both deployment values.

Local validation used committed code with frozen scripts and native tools; the
twelve existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete coverage,
in 66.8 and 66.5 seconds. The recorded random suite (root seed `20261026`,
sixteen cases, 2,048 attempts) accepted sixteen scenarios from sixteen
attempts without exclusions. All sixteen scenarios and 48 prefixes matched on
both levels in 94.9 and 93.5 seconds; they refunded every bank value and
covered both deployment values and the four generated completion patterns.
Neither run produced a finding.

A copied `importedHull` balance difference at `tx-2` of the funded
`identity-funded-refund` scenario was reduced on each level to that
transaction with zero flags, input, value and deployment value: six accepted
reductions in six candidate executions, all of whose actual comparisons
matched. The original and reduced archives replayed exactly with three-way
agreement (four replays), and synthetic replays reproduced the fingerprint.
Core or Hull fuel one was classified as inconclusive. With the extended
adapter, the two-slot storage, rollback, call, keyed, dynamic-array and log
fixed corpora still matched all 83 scenarios and 230 prefixes on each level.

This profile does not compare the sender's balance, gas, nonces or code, value
sent by contracts, values above the local sender's funds, or non-payable
methods, whose dispatcher rejects value with a 4-byte selector payload that
the Word outcome convention cannot express. Agreement is test evidence, not a
preservation proof.


## Compare bounded dynamic bytes

The `stateful-bytes` profile adds one bounded dynamic `bytes` value. Each
transaction calls `SynthesizedBytes.run(uint256 flags, bytes payload)`,
selector `0x220eb9b6`, with a payload of 0 to 64 bytes in the canonical
head/tail encoding: flags, the tail offset 64 relative to the arguments, the
length, the payload bytes and zero padding to a multiple of 32 bytes. The
calldata is therefore 100, 132 or 164 bytes long. The pinned dialect decodes
`bytes` only into memory, so the source parameter is `payload: memory<bytes>`
(`data` is a keyword). Its decoder follows the head offset, checks the range,
copies the length Word and the payload into fresh memory with `calldatacopy`
and zeroes the padding. Original Core reads calldata directly.

The contract reads `acc = sload(0)`. For each present 32-byte chunk `k`
(chunk 0 when the length exceeds 0, chunk 1 when it exceeds 32) it computes
`acc = step(acc + chunk_k)` with the checked aggregate step and writes slot
`1 + k`; in a chunk, payload bytes at or past the length read as zero. It then
writes `acc` to slot 0, adds the payload length to a running byte count in
slot 3 and writes the last payload byte, or zero for an empty payload, to
slot 4. The result is `sload(0) + sload(3) + sload(4) + calldatasize()`. Odd
flags revert with it as a 32-byte payload after the writes; other flags
return it. Shorter payloads leave slot 2, or slots 1 and 2, untouched.

### Definitions

These definitions were fixed before any execution.

- **Payload scope.** A payload has 0 to 64 bytes, including lengths that are
  not multiples of 32, and its calldata is exactly the canonical encoding
  above. Non-canonical offsets, truncated or longer payloads and nonzero
  padding are outside the profile. On truncated input the Rust decoder reverts
  with a 4-byte error that the Word outcome convention cannot express, while
  Core reads an absent Word or byte as zero.
- **Reading.** Original Core follows the head offset to the length with
  `inputDataWordBE?`. It reads each chunk Word the same way and masks it to
  the payload length, so padding never contributes. It reads the last payload
  byte with `inputDataByte?` and the calldata size with `inputDataSize`. Core
  and its host interface are unchanged. The source reads the decoded copy:
  the length as `mload(data)` and chunk `k` as `mload(data + 32 + 32k)`, which
  the decoder zero-padded. It reads the last byte as `mload(data + length) &
  255`, an unaligned load of the Word that ends at that byte; for an empty
  payload that Word is the zero length itself.
- **Committed observation.** After every transaction all three paths report
  status, payload and slots 0 through 4. The keyed profile's containment rules
  apply: the Hull and EVM paths must show no nonzero committed slot outside
  them. Memory is per call and not observed.
- **Committed comparison.** All three paths must agree on every observed field
  after every transaction. Each path must also follow the fixed protocol: the
  flags parity selects the completion and the payload is one Word. A revert
  keeps the prior slots. A returned transaction adds its payload length to
  slot 3, leaves its last payload byte (zero when empty) in slot 4 and returns
  the sum of the committed slots 0, 3 and 4 plus its calldata size.
- **Rollback.** A revert keeps the prior committed slots on every path, chosen
  by `ContractRuntime` for original Core. An incomplete transaction ends the
  sequence.
- **Deployment.** The constructor is empty and receives zero value. Every
  declared slot is zero afterwards, and no undeclared slot is nonzero on the
  Hull and EVM paths. Original Core starts from the declared post-deployment
  world.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, truncate one
  payload to a shorter length from the generation bank, set every byte of one
  payload to zero, or reduce one transaction's flags to their parity or clear
  its revert bit. They are ordered by transaction count, complete program
  complexity, total payload length, then the sum of all flags and payload
  bytes.

Generation draws three payload lengths from the bank 0, 1, 17, 31, 32, 33,
48, 63 and 64, a byte pattern for each (zeros, `0xff`, the ramp 1, 2, 3, ...
or seeded bytes) and one of four completion patterns from a separate high-bit
stream; flags are just the parity. Coverage adds two dimensions: the payload
lengths, and the payload lengths of reverted transactions, whose slot writes
rollback must discard. The chunk Words are the runtime inputs.

### Running and validation

```sh
lake build semanticBytesTool rustHullKeyedStorageScenario
mkdir -p .upstream/semantic-bytes-cases
.lake/build/bin/semantic-bytes-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-bytes-cases/corpus.json
python3 scripts/semantic-storage-campaign.py \
  --corpus scripts/semantic-bytes-corpus.json \
  --output .upstream/semantic-bytes-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-bytes \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-bytes-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as the other storage tools. Plans use `solcore-lean.bytes-plan.v1`
under the case field `bytesPlan`; cases use
`solcore-lean.semantic-bytes-case.v1`. Transactions are
`{id, flags, payload, calldata, value}`: `payload` is `0x` followed by two
lowercase hexadecimal digits per byte, and `value` is always zero. The tool
and the adapter both reject a payload longer than 64 bytes, a noncanonical
spelling and calldata that is not the canonical zero-padded encoding of the
saved flags and payload. The calldata of 26 generated transactions covering
every bank length matched `cast calldata "run(uint256,bytes)"` from the pinned
Foundry release byte for byte; the Lean tests retain two such vectors.
Histories use `solcore-lean.bytes-history.v1` with the dynamic-array history
fields, and the declared-slot Hull runner `rust-hull-keyed-storage-scenario`
serves the profile unchanged.

Generation reserves the measured 176-node wrapper before generating the step,
so the 384-node default leaves 208 nodes for it. 275 of the first 300 seeds
were accepted; the others drew a step template that does not fit. Generated
scenarios must complete with the prescribed outcomes and follow the length,
last-byte and sum protocol under original Core.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new payloads and flags,
and four generated seeds. Its expected histories were computed outside Lean by
a separate evaluator of the step programs and a direct model of the protocol.
`Tests/Main.lean` registers a validator that compares every status, payload
and slot with original Core. It rejects tampered outputs, byte counts and last
bytes, committed writes of a reverted transaction, and consistently re-encoded
payloads with a changed or appended byte. Required coverage is all 39 step AST
features in the corpus, the six storage boundary Words as chunks, one to three
helpers and transactions, all four templates, both outcomes, six completion
patterns, all nine bank lengths and reverted payloads of 0, 17, 32, 33 and 64
bytes.

Local validation used committed code with frozen scripts and native tools; the
fourteen existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete
coverage, in 73.5 and 73.4 seconds. The recorded random suite (root seed
`20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios from
eighteen attempts; its two exclusions drew a step template that does not fit.
All sixteen scenarios and 48 prefixes matched on both levels in 101.5 and
100.5 seconds. They covered every bank length, reverted payloads of 0, 1, 17,
31, 32 and 64 bytes and the four generated completion patterns. Neither run
produced a finding.

A copied `importedHull` difference in slot 2 at `tx-2` of the
`aggregate-pair-full-words` scenario was reduced on each level to that
transaction with zero flags, an empty payload and a reduced step: nine
accepted reductions in nine candidate executions, all of whose actual
comparisons matched. The original and reduced archives replayed exactly with
three-way agreement (four replays), and synthetic replays reproduced the
fingerprint. Core or Hull fuel one was classified as inconclusive. With the
extended adapter, the two-slot storage, rollback, call, keyed, dynamic-array,
log and call-value fixed corpora still matched all 95 scenarios and 263
prefixes on each level.

This profile does not compare gas, balances, nonces, code or memory, payloads
longer than 64 bytes, non-canonical offsets or padding, truncated input and
the decoder's revert paths, strings, `bytes` return values or nested dynamic
values. Agreement is test evidence, not a preservation proof.

## Compare value forwarded by contracts

The `stateful-forwarded-value` profile has one contract send value to another.
It installs `SynthesizedForwarder` and `SynthesizedRecipient`. Each transaction
calls the payable `SynthesizedForwarder.run(uint256 target, uint256 input,
uint256 amount)`, selector `0x24b912e5`, with a call value. The target Word is
the bound child address. The parent forwards `amount` to the child's payable
fallback through the pinned raw `call` wrapper; original Core's parent calls
`callContractWordWithValue` with the same value. The `stateful-calls` profile
already forwards zero or one unit from a fixed eight-unit endowment in
zero-value transactions. Here the sender funds the parent, and both the call
value and the amount come from the bank 0, 1, 7, 2^64 - 1, 2^64 and 2^70.

The parent adds the input and its call value to slot 0. It then calls the
child with the input as one raw 32-byte Word and value `amount`. The child
reads `old0` and `old1`, computes `step(input + callvalue + old0)` with the
checked aggregate step and writes it to slot 0, and adds its call value to
slot 1. An odd input makes it revert with that Word after both writes;
otherwise it returns it. The parent writes the child's payload to slot 1,
adding one if the child reverted, and returns `sload(0) + sload(1)`. Inputs
with bit two set make the parent revert with that Word after both writes. No
logs are emitted. Call modes are therefore `input & 3`: both return, the child
reverts, the root reverts, or both revert.

### Definitions

These definitions were fixed before any execution.

- **Value observation.** After deployment and after every transaction, all
  three paths report the root status and payload, and both contracts'
  balances and slots 0 and 1. Committed logs must be empty. The sender's
  balance is never observed: on the EVM path it also pays gas. Original Core
  runs each transaction through `BalancedTopLevelExecution`, which transfers
  the call value to the parent before the root runs, while the nested runtime
  transfers `amount` at the child call boundary. The imported-Hull runner
  performs the same top-level transfer in its checked ledger, and Hull's own
  call semantics move the forwarded value. The EVM path reads `eth_getBalance`
  for both contracts at each receipt block.
- **Funds.** The parent's empty payable constructor receives 2^72; the child
  deploys with zero value. Every call value and amount is at most 2^70, so the
  parent can always pay three forwards, and the local Anvil sender can pay
  the deployment and three call values. Original Core and imported Hull fund
  the caller with 2^80. A top-level transfer that original Core or Hull
  rejects is an execution error, never a revert.
- **Rollback and refunds.** A child revert discards the child's writes and the
  forwarded value: the child's committed account stays as it was, and the
  amount stays with the parent. A root revert, with or without a child revert,
  keeps both prior committed accounts and returns the call value to the
  sender. An out-of-fuel or otherwise incomplete transaction has unknown
  accounts and ends the sequence.
- **Deployment.** Both constructors are empty. Every path starts with the
  parent holding 2^72, the child holding zero, empty storage and no
  constructor logs. Original Core starts from that declared post-deployment
  world.
- **Committed comparison.** All three paths must agree on every observed field
  after every transaction. Each path must also follow the fixed protocol: bit
  two of the input selects the root completion and the payload is one Word. A
  root revert keeps both accounts, and a child revert under a committed root
  keeps the child's account. In every committed state the child's balance
  equals its slot 1, and the two balances sum to 2^72 plus the call values of
  every committed transaction so far.
- **Sequence reduction.** Candidates simplify the checked step (keeping every
  helper and binder), remove one transaction with stable IDs, replace one
  input by a bank input, clear its child or root revert bit, or lower one call
  value or amount to a smaller bank value. They are ordered by transaction
  count, complete program complexity, then the sum of all inputs, call values
  and amounts.

Generation draws, from a separate high-bit stream, three inputs from the
call profile's ten boundary inputs with their low two bits replaced by one of
the four call modes, and three call values and three amounts from the bank.
Coverage adds the call modes and four value dimensions: call values, forwarded
amounts, amounts a child revert returns to the parent, and call values a root
revert returns to the sender.

### Running and validation

```sh
lake build semanticForwardTool rustHullForwardScenario
mkdir -p .upstream/semantic-forward-cases
.lake/build/bin/semantic-forward-tool generate 0 384 2 512 1000000 \
  > .upstream/semantic-forward-cases/corpus.json
python3 scripts/semantic-call-campaign.py --profile stateful-forwarded-value \
  --corpus scripts/semantic-forward-corpus.json \
  --output .upstream/semantic-forward-ci --seconds 900
python3 scripts/semantic-suite.py --mode random --profile stateful-forwarded-value \
  --seed 20261026 --cases 16 --attempts 2048 --output .upstream/semantic-forward-random
```

The tool accepts the same `generate`, `emit`, `replay`, `observe` and `shrink`
commands as `semantic-call-tool`, with the same call bindings. Plans use
`solcore-lean.forward-plan.v1` under the case field `forwardPlan`; cases use
`solcore-lean.semantic-forward-case.v1`. Transactions are
`{id, input, value, amount, target, callee}`: `value` is the call value the
sender pays and `amount` the value the parent forwards, both at most 2^70.
Histories use `solcore-lean.forward-history.v1` with the call history's
fields. The call runner fixes the eight-unit endowment and zero top-level
value, so the new runner `rust-hull-forward-scenario` accepts `callerFunds`,
the fixed 2^72 endowment and per-call values and amounts in its
`solcore-lean.forward-contract-scenario.v1` scenarios. It reports a rejected
transfer as `transfer-rejected`. `semantic-call-differential.py` and
`semantic-call-campaign.py` select the profile by case schema or `--profile`.
Without explicit tools they use the profile's native tool and runner, and
`stateful-calls` keeps its schemas and rules. The calldata of 24 generated
transactions matched `cast calldata "run(uint256,uint256,uint256)"` from the
pinned Foundry release byte for byte; the Lean tests retain one such vector.

Generation reserves the measured 169-node wrappers before generating the step,
so the 384-node default leaves 215 nodes for it. 275 of the first 300 seeds
were accepted; the others drew a step template that does not fit. Generated
scenarios must complete with the prescribed root outcomes and satisfy the
refund and balance rules under original Core.

The fixed corpus has twelve scenarios and 33 transactions: eight imported
plans, which reuse the dynamic-array corpus steps with new inputs, call values
and amounts, and four generated seeds. Its expected histories, including both
accounts after every transaction, were computed outside Lean by a separate
evaluator of the step programs and a direct model of the protocol.
`Tests/Main.lean` registers a validator that compares every status, payload,
account and empty log list with original Core. It rejects tampered outputs,
balances and logs, a forward committed after a child revert, and changed call
values and amounts. Required coverage is all 39 step AST features in the
corpus, the ten boundary inputs, the four call modes, one to three helpers
and transactions, all four templates, both outcomes, every bank value as a
call value and as an amount, forwards of 1, 2^64 and 2^70 kept by child
reverts, and call values of 0, 7, 2^64 - 1 and 2^70 returned by root reverts.

Local validation used committed code with frozen scripts and native tools; the
fifteen existing native tools kept their hashes. The fixed suite matched all
twelve scenarios and 33 prefixes on Sonatina O0 and O2, with complete
coverage, in 71.2 and 77.4 seconds. The recorded random suite (root seed
`20261026`, sixteen cases, 2,048 attempts) accepted sixteen scenarios from
seventeen attempts; its one exclusion drew a step template that does not fit.
On O0 all sixteen scenarios and 48 prefixes matched in 98.1 seconds. They
covered every bank value as a call value and as an amount, child-revert and
root-revert refunds of every bank value, and all four call modes. On O2
fourteen scenarios and 42 prefixes matched. The other two, `generated-12` and
`generated-14`, crashed the compiler during O2 code-image export with
`Integer overflow when casting to usize`. Checked Hull export succeeded, and
both matched on O0. The O2 random gate therefore failed. Its findings are
recorded in the local `questions.md` without upstream investigation;
automatic reduction of the first kept the crash fingerprint within its attempt
limit.

A copied `importedHull` child-balance difference at `tx-2` of the
`three-helper-forwards` scenario was reduced on each level to that transaction
with zero input, call value and amount and a reduced step: nine accepted
reductions in nine candidate executions, all of whose actual comparisons
matched. The original and reduced archives replayed exactly with three-way
agreement (four replays), and synthetic replays reproduced the fingerprint.
Core or Hull fuel one was classified as inconclusive. With the extended call
and suite scripts, the two-slot storage, rollback, call, keyed, dynamic-array,
log, call-value and bytes fixed corpora still matched all 107 scenarios and
296 prefixes on each level. `scripts/test-source-call-rust.py`, run with the
cloned upstream, still matched all ten parent/child scenarios and 26
transactions.

This profile does not compare the sender's balance, gas, nonces or code,
forwards the parent cannot pay, value sent by the child, deeper or repeated
calls, or logs. Agreement is test evidence, not a preservation proof.

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
comptime and module combinations use the separate profiles below.


## Compare captured closures

The `runtime-closures` profile exercises runtime Word captures through actual
source lambdas and a generic higher-order `sc_apply<a>`. Both variants compute
an initial outer local with the original aggregate step, create a closure,
increment the outer local, and then increment it again after choosing the
second callable. `snapshot` reuses the first closure twice. `independent`
creates a second closure after the first increment. The first call receives
the original input, the second receives input plus one. The ABI result is
three times the first result plus the second result plus the current outer
local, so all captures, calls and outer assignments contribute.

The Core reference loads each captured Word before constructing its lambda.
The body uses that snapshot rather than reading the mutable outer cell. It
executes one direct closure application and one application through a checked
higher-order function. The entire original program passes the Core checker.
The pinned Rust implementation supplies the capture semantics being tested;
this profile does not claim equivalence with the separate native Lean source
frontend or prove source-emitter correctness.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-closures --seed 1 --nodes 384 --cases 12 --attempts 256 \
  --output .upstream/semantic-closures
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-closure-corpus.json --seconds 600 \
  --output .upstream/semantic-closure-ci
python3 Tests/scripts/test-semantic-closure-corpus.py
```

Native commands are `closure-generate SEED NODES COUNT ATTEMPTS FUEL` and
`closure-emit PLAN.json INPUT [FUEL]`. Schema `solcore-lean.closure-plan.v1`
retains a checked aggregate `stepProgram` and `variant` equal to `snapshot` or
`independent`. Cases contain both `closurePlan` and the complete applied
original Core `program`, with a full-program 512-node limit. Generation uses
zero, one, maximum Word and high-bit inputs and rejects constant generated
steps/references. Imported and reduced constant cases remain admissible.

Replay reconstructs the plan, source, input, original program, ABI and origin.
Shrinking preserves the capture recipe, step helper count and typed binders,
strictly decreases the full reference, and records a canonical parent witness.
The common campaign compares all three actual paths before accepting a
reduction. `closureRequirements.variants` and `closureCoverage` track the two
prescribed capture recipes only after matched execution; they are not measured
closure or opcode coverage. The AST feature/helper inventory describes the
original step and excludes the fixed capture/apply/ABI wrapper.

This profile is limited to fixed callable identities and Word snapshots.
Writes through captures, aggregate captures, escaped closure factories and
dynamic selection between different callable identities are separate scopes.
Comptime and source-module bundles use the separate profiles below.

The fixed closure corpus contains 24 cases across six plans. All matched across
the three real execution paths, covering nineteen step AST features, four Word
boundaries, all four aggregate recipes, one through three helpers and both
capture variants. Native validation also checked eight smaller candidates and
fifteen negative cases. A generated independent-capture case reduced in eight
accepted executions while retaining its maximum-Word input and failure
fingerprint. Original/reduced actual archive replay and synthetic replay passed;
an actual fuel-one run remained inconclusive. The attempt limit was recorded,
so reduction does not claim a globally minimal counterexample.


## Compare comptime expressions

The `runtime-comptime` profile retains two original Core ASTs: a closed G0 Word
expression and an aggregate step graph. Source renders the complete closed
expression inside `sc_constant`, which returns `comptime<word>`. Its result
passes through `sc_static(comptime value: word)`, also returning
`comptime<word>`, before use with runtime input. The emitter never evaluates
that expression itself or substitutes a Rust-computed result.

The independent Core reference evaluates the original closed expression once
to obtain `k`, then calls the runtime step once. The `offset` variant returns
`step(input + k) + k`; `scale` returns `step(input) * (k | 1) + k`. The odd
multiplier prevents a zero multiplier from discarding the step. All arithmetic
uses Word wrap. Both retained ASTs and the wrapper count toward the full
512-node limit and the whole-program typing check.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-comptime --seed 1 --nodes 384 --cases 12 --attempts 256 \
  --output .upstream/semantic-comptime
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-comptime-corpus.json --seconds 600 \
  --output .upstream/semantic-comptime-ci
python3 Tests/scripts/test-semantic-comptime-corpus.py
```

Native commands are `comptime-generate SEED NODES COUNT ATTEMPTS FUEL` and
`comptime-emit PLAN.json INPUT [FUEL]`. Schema `solcore-lean.comptime-plan.v1`
contains `constantProgram`, `stepProgram` and `variant` (`offset` or `scale`).
The case carries `comptimePlan` and the full applied Core reference. Generation
records both seeds and node allocations, reserves at most eight nodes for the
generated constant, requires an actual operation in that AST, and uses the
four standard boundary inputs. Random comptime campaigns default to 512
generation attempts; other profiles retain 256. Larger imported constants
remain supported within the full-program budget. Constants still render only
the original scalar operations, so other constant operations and fuel
exhaustion remain explicit exclusions; step functions render the raw
primitives. Imported and
reduced constants may be literals.

Replay reconstructs both ASTs, source and wrapper, independently of any saved
observation. Shrinking may reduce the closed constant, step or runtime input;
every candidate is rechecked, keeps its variant and step binder inventory,
and strictly decreases the full reference. A canonical parent witness supports
replay of each reduced case. Actual three-way execution determines whether a
candidate retains an observed failure.

`provenance.features` describes the original step AST;
`provenance.constantFeatures` describes the original closed expression. Fixed
corpora specify `requiredConstantFeatures` and each entry's
`expectedConstantFeatures` separately. `constantCoverage` counts only completed
three-way agreement. `comptimeRequirements.variants` and `comptimeCoverage`
require both composition recipes. These inventories describe source inputs,
not measured backend opcodes. Passing a runtime value to a comptime parameter
is outside this profile; an actual negative probe is rejected during Rust's
comptime evaluation with `SC0409`.

Comptime source-emitter correctness is tested, not formally proved. This
profile does not unify the native Lean frontend's own staging evaluator or
claim unrestricted cross-stage persistence. The module profile below combines
this staging boundary with imported generics and captured closures.

All 32 fixed comptime cases across eight plans match the three real execution
paths. Coverage includes all fifteen enabled constant AST features, 21 step AST
features, both variants, four boundary inputs, one through three helpers and
all four step recipes. Native validation checks eleven smaller candidates and
twenty negative cases. A scale case reduced both retained ASTs in twelve
accepted executions while keeping its maximum-Word input and synthetic
fingerprint. Original/reduced archive replay and synthetic replay passed;
actual fuel-one execution remained inconclusive. All 64 saved cases from the
eight earlier pure profiles retained identical native artifacts and results.


## Compare module bundles and mixed features

The `runtime-modules` profile emits four flat files with explicit imports and
exports. Every provider contributes to the returned Word:

| File | Role |
| --- | --- |
| `case.sol` | ABI entry, staged constant, ordered provider calls and generic selection. |
| `common.sol` | Original closed constant expression, comptime parameter/return, generic apply and select. |
| `left.sol` | Original aggregate step, a Word snapshot closure and mutation of its outer local. |
| `right.sol` | A distinct Word snapshot closure, input-dependent capture and outer mutation. |

Let `k` be the original closed constant, and `x` the runtime input. The left
provider captures `step(x + k)`, increments its outer local, and combines a
closure call with that current local. The right provider captures `x ^ k`,
increments its outer local by two, and likewise combines its closure result
with the current local. Both providers pass a closure through the imported
generic apply function. After both return, an imported generic selector chooses
left for odd input and right for even input. The final Word is selected plus
left plus three times right plus `k`. Both captures and every provider therefore
remain observable even when one selector branch is not taken.

The Core reference retains both original ASTs, creates actual snapshot lambdas,
and evaluates the corresponding fixed composition. It does not parse the
emitted files or reuse Rust's specialized constants, closures or function IDs.
The full program is checker-sealed; the module emitter's meaning preservation
remains unproved.

```sh
lake build semanticCaseTool rustHullScenario
python3 scripts/semantic-campaign.py \
  --profile runtime-modules --seed 1 --nodes 384 --cases 16 --attempts 512 \
  --output .upstream/semantic-modules
python3 scripts/semantic-campaign.py \
  --corpus scripts/semantic-module-corpus.json --seconds 900 \
  --output .upstream/semantic-module-ci
python3 Tests/scripts/test-semantic-module-corpus.py
python3 scripts/test-semantic-source-bundle.py
```

Native commands are `module-generate SEED NODES COUNT ATTEMPTS FUEL` and
`module-emit PLAN.json INPUT [FUEL]`. A `solcore-lean.module-plan.v1` plan retains
`constantProgram` and `stepProgram`; the composition is fixed and has no
variant field. All 512 permitted nodes include both ASTs and the composition.
Random generation reserves at most eight nodes for the constant and defaults
to a 512-attempt campaign limit. All four boundary inputs are emitted per
accepted plan. Constant/step/input shrinking retains typed step binders,
strictly decreases the full original program, and regenerates all four files.

Each `solcore-lean.semantic-module-case.v1` case has `modulePlan`, the applied
Core `program`, the usual input/ABI/provenance fields, and `sourceBundle`:

```json
{
  "schema": "solcore-lean.source-bundle.v1",
  "entry": "case.sol",
  "files": [
    {"path": "case.sol", "source": "..."},
    {"path": "common.sol", "source": "..."},
    {"path": "left.sol", "source": "..."},
    {"path": "right.sol", "source": "..."}
  ]
}
```

The names and ordering are fixed, and `source` is a byte-identical alias of the
entry text. Native replay reconstructs every file and its import/export graph.
Changed providers, missing/extra files, noncanonical names and mismatched entry
aliases cannot pass replay.

Hull's span-derived source inventory may omit a loaded provider after staging
or optimization. The adapter therefore saves and hashes all four generated
files independently before and after both exports. It also checks the complete
tracked pinned standard-library source inventory. The fresh source root is
flat; extra source files, directories and symlinks are rejected. A generated
source URI is recognized only by its exact recorded URI, never by basename or
suffix. Library URIs and hashes remain separate.

`sourceBundleReceipt` retains all relative file hashes, their original URIs and
the pinned library inventory. Replay verifies every archived provider even if
it is absent from Hull spans, then compares generated hashes by canonical
relative name. It does not read the former source directory. An archive can
therefore be moved before replay, while the pinned library/tool identities must
remain unchanged:

```sh
python3 scripts/semantic-differential.py --case CASE.json --output .upstream/module-run
mv .upstream/module-run .upstream/module-archive
python3 scripts/semantic-differential.py --replay .upstream/module-archive \
  --output .upstream/module-replay
```

The fixed corpus requires both prescribed selection branches through
`moduleRequirements.branches` and `moduleCoverage`. Step and original constant
features remain separate inventories, as in the comptime profile. These are
source recipe inventories, not measured import, specialization or opcode
coverage. The scope is this fixed four-file graph, Word captures and ABI Word
results; arbitrary module graphs, cyclic imports, dynamic ABI and native Lean
frontend equivalence are outside it.

All 32 fixed module cases across eight plans match the three actual execution
paths, with no errors, rejections or inconclusive cases. Coverage includes 21
step AST features, all fifteen closed-constant features, one through three
helpers, four boundary inputs, four generation recipes and both prescribed
selection branches. Native validation checks eleven smaller candidates and 31
negative, tamper, path and fuel cases. All 72 saved cases from the nine earlier
pure profiles retain identical native artifacts and observations.

Exact archive replay passed after relocation to a path containing spaces and
removal of the old directory. A synthetic mismatch accepted twelve reductions
in twelve executions, reducing both constant and step while retaining its
maximum-Word input and fingerprint. Actual reduced archive replay matched;
synthetic replay preserved the finding. This bounded search makes no global
minimality claim. Fuel-one execution was inconclusive. Missing archived
provider inventory and an extra `foreign.sol` were rejected before processes
started.

The full repository build (9,900 jobs), tests and semantic-kernel check passed,
as did 33 protocol, 61 campaign and ten source-bundle regressions. M6 is complete
for its bounded generic, closure, comptime and module profiles. These results
do not prove source-emitter preservation or language-wide compiler correctness.
