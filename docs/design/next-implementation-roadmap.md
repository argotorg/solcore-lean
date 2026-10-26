# Next implementation roadmap

Updated: 2026-10-26. This is the implementation order after the bounded M0–M6
milestones. Delivery and verification are recorded separately below.

## Baseline

[M0–M6](semantic-differential-testing.md) provide checked generation, source
emission, three-way execution, bounded campaigns, failure-preserving reduction
and strict replay. The primary oracle executes the original generated Core;
the other paths execute Rust-produced EVM bytecode and imported Rust Hull.
Generated EVM comparisons support Sonatina O0 and O2. The initial thirteen-
profile O0/O2 and ten-profile pure Yul gates passed. The new primitive profile
is connected to the runners; its random O2 gate exposed a compiler crash.
The separate upstream fixture harness also
runs Yul; its results are distinct from generated semantic campaigns.

Fourteen pure profiles and three stateful profiles are available locally. The
[CI workflow](../../.github/workflows/semantic.yml) and
[suite commands](../../scripts/SEMANTIC_CI.md) connect the fixed and random
runners with shared limits, preparation and retained findings. Hosted execution
still requires publishing the workflow. M6d's 32 fixed cases all agreed, its
original and reduced archives replayed, and relocation of a four-file archive
was verified. The completed milestone document records the earlier evidence.

Core typing is proved for admitted programs. Source-emitter preservation,
native Source whole-compiler preservation and the remaining Hull public
connections are separate proof obligations. None follows from agreement in a
test corpus.

## Ordered priorities

| Order | Deliverable | Status | Completion boundary |
| --- | --- | --- | --- |
| 1 | CI and continuous bounded random campaigns across all existing profiles | Local gate complete; hosted run pending | Reproducible CI jobs, scheduled seed exploration, retained findings and verified cancellation/resource limits. |
| 2 | Generated Sonatina O2, then Yul comparisons | Local gate complete | The same original cases run on each enabled backend with explicit backend provenance and replay. |
| 3 | Missing runtime operation mappings | Implemented; O2 random run has a recorded finding | Tested Rust-dialect mappings, dynamic-input regressions, generation, reduction and replay for each added operation. |
| 4 | Richer generated grammar | Call-graph, loop and aggregate families validated locally; hosted run pending | Broader typed compositions with bounded generation and reductions that preserve binding, effects and failure identity. |
| 5 | A minimal proof for the actual Rust-dialect emitter | Scalar renderer and both scalar wrappers proved locally; other emitters open | A small connected meaning-preservation theorem for what is actually emitted, not for a substitute native Lean syntax. |
| 6 | State and ABI extensions | Keyed-storage and bounded dynamic-array extensions validated locally; hosted run pending | Explicit additional observations and transaction semantics, with actual three-way tests and sequence reduction. |
| 7 | Native Source goal two | In progress: statement closure over the actual compiler tree; expression closure and public connection remain | Complete accepted-body preservation and connect all actual passes to the public session. |
| 8 | Remaining Hull public connections | In progress: identity, SHA-256 and RIPEMD-160 precompiles connected | Independent semantics through actual lowering, initialization and public execution for each remaining feature. |

Complete each operational connection before starting the next large expansion.
An ambiguous comparison or confirmed defect can justify a narrowly scoped
proof or implementation fix sooner; record that reason and return to this
order. Keep existing profile behavior and saved-case semantics stable, or
version a deliberate change explicitly.

## 1. CI and continuous bounded random campaigns

Use the existing runners, rather than creating another execution oracle:

- `semantic-campaign.py`: `closed-g0`, `runtime-word`, `runtime-functions`,
  `runtime-mutation`, `runtime-aggregates`, `runtime-loops`, `runtime-generics`,
  `runtime-closures`, `runtime-comptime` and `runtime-modules`.
- `semantic-storage-campaign.py`: `stateful-storage` and
  `stateful-storage-rollback`.
- `semantic-call-campaign.py`: `stateful-calls`.

Separate a predictable pull-request gate from longer scheduled exploration.
Use fixed corpora for the gate and recorded, deterministic seed ranges for
random runs. Every profile must receive a nonzero exploration allocation;
slow profiles must not silently disappear when a shared wall-clock limit is
reached. Keep the current pinned Rust/compiler/backend/stdlib/EVM identities.
Changing that reference is a separate migration.

Acceptance criteria:

1. A clean CI checkout can provision the pinned tools, build the required Lean
   executables and run all fixed corpora. Cache keys include toolchain and
   source identities; cached artifacts do not bypass existing provenance
   checks. A local command reproduces the CI matrix.
2. Pull-request and scheduled jobs have explicit time, disk, case, generation,
   execution and reduction limits. Cancellation cleans child processes,
   loopback Anvil instances and disposable files. Resource exhaustion is
   reported as incomplete, never as a match or an empty successful campaign.
3. Reports distinguish generation exclusions, accepted cases, matched cases,
   mismatches, source/backend rejection, adapter errors and resource outcomes.
   Expected generator exclusions may occur, but requested work or required
   coverage that was not completed cannot pass the gate.
4. Scheduled runs record seed ranges and profile budgets so interrupted work
   can be reproduced without repeating only a fixed initial range forever.
   Tests never send transactions to an existing or remote chain.
5. Retain compact summaries for successful runs and complete replay archives
   for findings, including source bundles, original Core, transactions,
   observations, tool hashes and reduction history. Set artifact retention
   limits. Demonstrate replay from a fresh checkout with restored tools.
6. Exercise a controlled mismatch and a resource failure through the CI commands. Confirm
   reduction preserves the fingerprint, raw actual observations remain
   untouched by synthetic tests, and non-success outcomes produce the intended
   job result. Do not describe continuous testing as operational until the
   checked-in workflow has completed a real run.

Implemented operational components:

- `prepare-semantic-tools.py` verifies the installed pinned toolchains, fetches
  only the exact Rust revision when network access is explicitly enabled,
  builds exporters offline and eight native tools once, and records input and
  binary hashes. A new checkout and initially absent Cargo target were tested.
  Subsequent offline verification and preparation reuse the recorded tools.
- `semantic-suite.py` dispatches all thirteen existing profiles. Fixed mode
  requires complete manifests; random mode records derived profile/shard seeds.
  Shared time/disk limits, per-profile counts and throughput, retained findings
  and owned subprocess cleanup are independent of the comparison oracle.
- `check-semantic-findings.py` exercises actual three-way execution, a separate
  synthetic mismatch, accepted reduction, exact reduced replay, synthetic
  replay and real Core fuel exhaustion. Both existing tools and the freshly
  built Rust tools passed all four phases; actual observations remain intact.
- The workflow uses fixed action commits and read-only repository permissions.
  Pull requests and `main` pushes run fixed gates; daily/manual runs add new
  recorded seeds. Reports and findings have fourteen-day retention. Local
  workflow syntax validation does not claim a completed GitHub-hosted run.

The full Lean build (9,900 jobs), registered tests, semantic-kernel policy,
272 Python policy tests and workflow syntax validation passed. The Python
checks include real subprocess timeout/interruption cleanup. All 312 fixed
cases/scenarios passed across thirteen profiles, including 98 matched stateful
transaction prefixes. Random seed `20261026`, sixteen cases per profile and
2,048 generation attempts per profile produced 208 matches and 144 matched
stateful prefixes. The random run recorded 1,850 generation exclusions and no
generation resource exclusions. Both suites had zero mismatches, errors,
rejections, inconclusive results, missing coverage or unexecuted cases.

The fixed run took 1,689.136 seconds and retained 21,386,536 bytes; the random
run took 1,115.700 seconds and retained 13,572,210 bytes. These local runs
overlapped each other and a cold tool build, so their timings are observations,
not CI performance guarantees. The operational implementation is complete;
the first hosted workflow run remains to be observed after publication.

## 2. Generated Sonatina O2, then Yul

First add Sonatina O2 while retaining O0 as a separate result. Then add Yul
compiled by a pinned solc. Start with the existing pure Word ABI and extend
the backend matrix to stateful profiles only after their deployment, receipts,
rollback, logs and storage comparisons are connected.

Acceptance criteria:

1. Each backend compiles the same emitted source bundle through the actual
   checked Rust path. Neither backend's result supplies the direct Core
   oracle. Record backend, optimization flags, compiler versions and exact
   artifact hashes; select them explicitly during replay.
2. Compare each enabled EVM result with original Core and the corresponding
   imported-Hull execution. Keep backend-specific observations separate so
   an O0 pass cannot hide an O2/Yul difference or skipped compilation. Any
   subset not yet enabled is stated explicitly in the matrix.
3. Replay and reduction preserve the selected backend matrix and the paths
   involved in the finding. Add original and reduced archive regressions for
   backend differences, rejection, resource exhaustion and missing results.
4. Run the fixed corpora plus bounded random seeds on O2 before enabling it in
   CI; repeat for Yul. Stateful comparisons use actual mined transactions and
   committed histories, not a pure `eth_call` replacement. No equality of gas,
   bytecode layout or optimizer internals is required by these profiles.
5. Existing O0 cases and replay behavior remain valid. A changed exact tool
   hash may require a fresh run from the saved case; never silently accept an
   archive produced by different tools as exact replay.

O2 implementation is connected across all thirteen profiles. `--backend
sonatina-o2` selects the actual Sonatina optimization pipeline; each report,
failure fingerprint and reduced run retains the selection. Exact replay
inherits it and rejects a conflicting override. Exported image metadata,
sidecar provenance and the Lean decoder check the pinned backend and admitted
optimization level. The same compiler executable supports both levels.
The CI matrix keeps O0 and O2 jobs and artifacts separate. The O2 fixed suite
passed all 312 cases/scenarios across thirteen profiles, including 98 stateful
transaction prefixes, with zero mismatches, errors, rejections, incomplete
cases or missing coverage. It took 1,621.804 seconds locally and retained
19,552,501 bytes. This completed the local O2 gate; hosted execution still
requires publication and observation of a real workflow run.
The O2 random suite passed all 208 cases/scenarios across thirteen profiles
with seed `20261026`, sixteen cases and 2,048 attempts per profile. It recorded
1,850 generation exclusions, zero resource exclusions, 144 matched stateful
transaction prefixes and no mismatches, rejections, errors, incomplete cases
or missing coverage. Its local elapsed time was 1,074.688 seconds and retained
output was 12,333,641 bytes, overlapping the fixed suite and other validation.

The exporter/decoder boundary passed focused Lean checks, four Rust unit tests
and six Python protocol tests. Real default and explicit O0 exports were
identical; O2 changed the bytes while preserving the exact embedded-child
ranges and the same checked Hull. The eight native tools built successfully.
The full Lean build (9,900 jobs), registered tests and complete Python policy
suite (303 tests) passed. The eight native executable hashes were unchanged
by the full build/test run. Default-O0 regression
across closed values, runtime inputs and nested calls passed all 46 cases.

The O2 finding check passed actual execution, accepted synthetic reduction,
exact reduced archive replay, synthetic replay and fuel-one classification.
Separate storage, rollback and call checks accepted six reductions each:
committed slot zero, reverted output and ordered log data respectively.
Original and reduced archives all replayed with inherited O2 and actual
three-way agreement (six exact replays); three reduced-case synthetic replays
preserved the backend, transaction identity and mismatch fields. These
controlled differences do not represent upstream bugs.

### Initial Yul boundary

The initial generated Yul comparison is restricted to pure Word ABI profiles.
Compile the checked Rust driver's Yul through solc
`0.8.35+commit.47b9dedd`, with its optimizer enabled and Osaka selected. The
same standard-JSON compilation must supply both creation and deployed bytes.
Record the exact Yul, compiler input/output, flags, tool hashes and selected
wrapper. Verify the deployed bytes on the local EVM and retain all artifacts
needed for exact replay and reduction.

Solc does not supply the complete named child-offset map expected by the
current Hull code-image importer. Actual probes showed omitted unused children
and two distinct identical children sharing one physical offset, including
with optimization disabled. Assembly source spans are not byte offsets.
Consequently, the initial comparison reports three explicit paths:
original generated Core, actual Yul EVM, and imported Hull linked with Sonatina
O0 images. The last is an additional reference for the same pure result, not
Yul-linked Hull execution. Do not infer a linker map by searching byte strings,
mislabel Sonatina images as Yul, or weaken the code-image invariant.

Admit only the generated creation/runtime wrapper pair with actual runtime
output and no unresolved libraries or immutable references. Stateful Yul,
code-observing programs and arbitrary nested objects remain excluded until
their layout and observation boundary are connected explicitly. This scope
does not require bytecode-layout or gas equality between the three paths.

Before adapter integration, eight real Yul EVM probes matched freshly replayed
original Core: addition, an input-dependent high-bit branch, ordered local
mutation, a seven-iteration loop, both closure capture variants, comptime and
the four-module bundle. Every deployed runtime matched the bytes from the same
solc compilation; bundle and pinned library hashes were audited. This probe
does not establish the campaign/replay connection or Yul-linked Hull execution.
The separate exporter passed thirteen protocol and process tests, including
termination of a compiler that ignores graceful cancellation.
The evidence transport passed eleven policy tests and an actual export moved
to a new directory containing spaces after the original location was removed.
It checks the main Hull bytes and sidecar as well as the separate Yul Hull,
reconstructs the exact solc input from saved Yul and settings, and derives the
accepted bytes again from the retained solc output. These artifact checks complement the execution gate below.

The normal adapter, campaign, reduction, exact replay and suite now accept
`--backend yul` and `--solc`. Default Yul suites select exactly ten pure
profiles; explicit stateful requests fail before execution. The complete
Python policy suite passed 345 tests. The real finding check passed reduction,
exact replay, repeated synthetic fingerprint and fuel-one classification.
An actual four-module archive was moved to a path containing spaces, its old
location removed, and replayed with three-way agreement and the same Yul byte
artifact. Three accepted module reductions retained the finding; the final
actual replay agreed on all paths. Fresh Word and nested-call regressions
also agreed for both Sonatina levels (four runs). The CI Yul job uses a pinned,
SHA256-checked official solc binary. The random Yul suite passed all 160 cases
across ten profiles with seed `20261026`, sixteen cases and 2,048 attempts per
profile. It recorded 1,274 generation exclusions, zero resource exclusions and
no mismatches, errors, rejections, missing coverage or unexecuted cases. Local
elapsed time was 1,279.008 seconds and retained output was 9,999,222 bytes,
overlapping fixed-suite validation and other checks. The fixed Yul suite passed
all 276 cases across the same ten profiles, with zero mismatches, errors,
rejections, inconclusive results, missing coverage or unexecuted cases. It took
2,248.763 seconds and retained 20,489,590 bytes locally. This completes the
initial local Yul gate; no hosted-run result is claimed.

## 3. Missing runtime operation mappings

Core and imported Hull already execute more operations than the generated
source renderer admits. Extend the renderer in small groups: unsigned
division/remainder; signed comparison/division/remainder; logical/arithmetic
shifts; byte selection and sign extension; exponentiation and leading-zero
count; then modular addition/multiplication. Confirm exact source spellings
and parameter order in the pinned Rust standard library before choosing a
mapping. Do not infer compatibility from a familiar operator name.

Acceptance criteria for each group:

1. Record the original Core operation, exact Rust source expression or builtin,
   operand order, Word/signed interpretation and exceptional cases. Preserve
   left-to-right operand evaluation and snapshot values before later effects.
2. Add dynamic-input fixtures so the operation cannot be tested only by
   compile-time folding. Cover zero divisors/moduli, Word wrap, signed minimum
   and maximum, minimum divided by minus one, shifts at and beyond 256,
   byte/sign-extension boundaries and zero exponent/base where applicable.
3. Execute those fixtures through original Core, actual Rust EVM and imported
   Hull, for every enabled backend. Use the independent Core result and
   hand-known boundary cases, never a Rust-evaluated expected constant.
4. Integrate generation, explicit unsupported exclusions, typed shrinking,
   strict case reconstruction and fixed-corpus requirements. Preserve older
   generator/emitter versions or version changed output. Demonstrate a
   reduction and exact replay involving the new operation.
5. Distinguish AST inclusion, observed branch/result coverage and actual
   runtime opcode coverage. Make the last claim only with execution evidence;
   optimizer folding or lowering may remove the expected opcode.

The `runtime-primitives` profile is now connected to the ordinary CLI,
adapters, campaigns and suites after the Yul gate passed. It reuses sealed
`CheckedWordFunction` values and executes the original applied Core program.
The source imports explicit aliases from `std.opcodes`; the following table
describes those raw functions, not similarly named public convenience wrappers.

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

Each operand is evaluated and stored in a fresh temporary in original Core
order before the call is formed. Public `std.addmod` and `std.mulmod` reject a
zero modulus, so they are not substitutes for the raw aliases above. Byte and
sign extension already use index-first Core operands and must not be reversed.
The Core exponent implementation uses repeated modular squaring, so a Word
exponent does not require constructing the unbounded mathematical power.

The new renderer's focused build and 155 original Core boundary applications
passed, including exact source checks for order and aliases. Cases additionally
check canonical source/provenance, binding-aware shrink/replay, a full applied
program budget of 8–512 nodes, and eight generator inputs: 0, 1, 2, 255, 256,
maximum Word, high bit and high bit minus one. Generated functions must vary
across that bank; imported boundary cases may legitimately be constant.
A separate preintegration check then ran twenty canonical cases through actual
O0 and O2 execution: all forty comparisons agreed across original Core, Rust
EVM and imported Hull. It exercised all fourteen new operations while keeping
the eight existing native executables unchanged. This is narrower than the
full fixed/random profile gate, which remains pending.
The prepared fixed corpus contains 81 cases from 34 functions, with handwritten
Core results and seventeen distinct inputs. It covers all fourteen additions
and the required eight generator boundaries. The native corpus validator
confirmed all 81 results, deterministic source/replay, 319 strictly smaller
typed candidates and six malformed-corpus rejection checks. The registered fixed corpus adds 81 cases: full suite totals are now 393
for each Sonatina level and 357 for pure Yul. All 81 new fixed cases passed on
all three backends. Their local suite times were 409.522 seconds (O0), 410.716
seconds (O2) and 646.389 seconds (Yul), overlapping each other and other checks.

For root seed `20261026`, sixteen cases and 2,048 attempts, O0 and Yul matched
all sixteen cases. O2 matched eight and crashed compilation on eight inputs of
one generated function. The campaign correctly returned failure and preserved
original/reduced archives. Automatic reduction isolated a large constant
arithmetic shift and retained the compiler-crash fingerprint. The original
Core result is independent of this compiler. This is a genuine upstream
finding recorded for later review, not a successful O2 random gate. Per the
user's instruction, investigation and fixes are deferred; the operator and
failures remain in generation and reporting.

After CLI activation, all 286 retained old-profile cases (276 fixed and ten
random) replayed with identical complete JSON and original Core observations.
The other seven native tools retained their previous hashes. The full Python
policy suite passed 358 tests. The source library build and full registered
Lean test driver passed, including all 81 new corpus observations and 319 typed
shrinks; those builds left the eight native tool hashes unchanged. A primitive
multiplication-modulo case passed
actual three-way execution, two accepted synthetic reductions per backend,
original and final exact archive replay (six replays), and repeated synthetic
fingerprints on O0, O2 and Yul. All raw runtime reports remained actual matches;
these controlled differences are test infrastructure checks, not upstream bugs.

## 4–8. Subsequent work

**Richer grammar:** vary typed expression and body composition beyond the
current fixed recipes. Add one family at a time, retaining alias/evaluation
order and binder-aware shrinking. Prefer finite acyclic calls and bounded
loops before unrestricted recursion. Unsupported combinations stay explicit.

The first family will generate `runtime-call-graphs`: one to three acyclic
Word-to-Word helpers, with Word/Bool expressions generated directly in the
runtime parameter's scope. Calls may refer to any earlier helper, occur inside
operands and local bindings, and appear in either branch. Include shared
callees, skipped helpers, nested call arguments and the primitive operations
from priority 3. The current fixed immediate-predecessor chains remain valid
under their existing versions. Reuse the full Core checker and typed DAG
reduction; record fresh schema/generator/emitter versions for the new family.

Its gate requires bounded deterministic generation with an actual complete
program node limit, named call-graph fixtures, strict replay and reduction,
and agreement under O0, O2 and Yul. Report generation yield and syntactic call
edges separately from runtime coverage. Prepare new modules in isolation while
the primitive gate runs, then connect the ordinary runners only after that gate
passes. Aggregate and bounded-loop consumers of this richer grammar follow as
separate changes; this first family alone does not complete priority 4.

The first family is now connected to the ordinary case tool, adapters,
campaigns and suites. Generation uses a fresh typed grammar, measured complete
program budgets and the existing sealed Core DAG. A 256-seed structural census
covered all thirty features and nine call shapes. The fixed corpus contains
56 cases from 26 original graphs, eleven distinct inputs including the required
eight, all three helper counts and all nine call shapes. Native validation
confirmed every handwritten Core result, source invariance across inputs,
224 strict typed reductions/replays and sixteen malformed/fuel checks.

Focused Lean builds, the source library and the full registered Lean test
driver passed. The full Python policy suite passed 372 tests. All 368 retained
older cases replayed with identical complete JSON and Core observations; the
other seven native tools kept their hashes.

All 56 new fixed cases passed on O0, O2 and Yul, including the required AST
features, inputs, helper counts and nine call shapes. Local suite times were
284.172, 284.635 and 455.645 seconds respectively. Random seed `20261026`,
sixteen cases and 2,048 attempts produced seven ordinary generation exclusions
and no resource exclusions on each backend. O0 and Yul matched all sixteen;
O2 matched eight and recorded eight compiler crashes with the same host integer
conversion panic observed by the primitive profile. That O2 random gate failed.
Per the user's instruction, the symptom is recorded without further upstream
investigation or a backend patch. Local random suite times were 83.439, 158.625
and 131.550 seconds respectively, overlapping other validation.

A shared-callee diamond passed four accepted typed synthetic reductions on
each backend (twelve total), retaining all three helper bindings. Original and
final exact replays all matched (six), synthetic fingerprints reproduced on
all three backends, and fuel-one executions were correctly inconclusive.
The raw actual reports remained unchanged. Suite totals are now 449 fixed
cases/scenarios for Sonatina and 413 pure cases for Yul; the existing and new
families were validated in separate runs. Hosted CI still has not been run.

The second family, `runtime-call-graph-loops`, is now connected to the
ordinary case tool, adapters, campaigns and suites. Its checked plan reseals an
unchanged `CheckedWordFunctionDAG` through `Aggregates.CheckedDAG.ofParts?`
and `BoundedLoop.CheckedPlan.ofParts?`, and retains equality between the scalar
helpers/entry and the executed loop step. It reuses the finite ordinal-guard
Core reference and its typing; no evaluator or Core primitive was added. A
separate emitter prints the arbitrary entry as `sc_step` with
`CallGraphRenderer` and raw primitive aliases; `LoopEmitter` is unchanged.

Generation selects mask one, three or seven, subtracts the measured wrapper
overhead of 26, 50 or 98 nodes from the complete budget, generates the step
with the call-graph grammar and remeasures the full application. Admission
requires an entry call, step results varying over the eight primitive inputs
and a positive-trip loop input whose result changes. Imported and reduced plans
may use mask zero. Native tests check exact overhead accounting, agreement of
the loop reference with repeated scalar graph applications for 64 generated
plans, canonical provenance, tampering rejection, strict replay and typed
reductions that keep every helper binding and never raise the mask.

The fixed corpus contains 66 cases from eleven plans, eight imported and three
generated, at the six loop inputs. Its expected Words were computed outside
Lean from EVM Word semantics and the loop definition; native validation
confirmed all 66 against original Core and replayed 264 strictly smaller typed
reductions. It covers all thirty scalar AST features, one to three helpers,
the nine call shapes, and masks and iterations zero, one, three and seven.

Focused Lean builds, the source library (9,920 jobs) and the full registered
Lean test driver passed. The full Python policy suite passed 404 tests. All
425 retained older cases replayed with identical complete JSON and Core
observations; the other seven native tools kept their hashes.

All 66 fixed cases matched on O0 and Yul with complete feature, input, helper,
mask, iteration and call-shape coverage. The first O2 fixed run matched 65; the
other case stopped with a host `Operation not permitted` error raised inside
the adapter before any execution path ran, while parallel suites and
process-spawning tests heavily loaded the machine. A fresh O2 run matched all
66. The error came from `killpg` on a process group holding only an exited,
unreaped member, which macOS can report as `EPERM`; the suite runner already
tolerated it. The adapter and Yul exporter now tolerate it as well, with
regression tests. The failed run remains retained locally.
Local fixed times were 415.034 seconds (O0), 421.204 seconds (O2 rerun) and
618.790 seconds (Yul), overlapping other runs. Random seed `20261026`, sixteen
cases and 2,048 attempts accepted three plans from fourteen attempts, using
masks one, three and seven, with eleven ordinary exclusions and no resource
exclusions. All sixteen cases matched on each backend, in 95.945, 97.129 and
153.216 seconds. This allocation did not reproduce the O2 compiler panic
recorded for the primitive and call-graph families.

A seven-iteration, three-helper fixed case passed controlled synthetic
reduction on each backend: twelve accepted typed reductions kept every helper
binding and the mask. Original and final archives replayed exactly with
three-way agreement (six replays), synthetic fingerprints reproduced and
fuel-one executions were inconclusive. Raw actual reports remained matches.
Suite totals are now 515 fixed cases/scenarios for Sonatina and 479 pure cases
for Yul. Hosted CI still has not been run.

The third family, `runtime-aggregate-call-graphs`, composes internal Word
pairs, Word sums, projections and case payload scopes with helper calls in the
same directly generated typed expressions; it does not reseal a scalar graph.
Generation tracks Word, Bool, pair and sum locals, charges each typed form its
measured minimum and seals the graph with the existing aggregate DAG checker.
A new renderer keeps the call-graph scalar, primitive and call formatting
(checked identical on scalar bodies) and the aggregate tuple, sum and match
forms. Reduction reuses the typed aggregate reductions, which keep every
helper, typed let and payload scope. A nine-shape structural inventory records
calls in pair components, sum payloads, projections, case scrutinees, case
branches and payload arguments, plus aggregate lets, aggregate branches and
nested cases. Generated graphs need an entry call and at least one call
composed with an aggregate value or payload; private cells and Unit values stay
in the older template profile.

A census of 288 generated graphs covered all nine shapes with no checker or
budget-invariant failure. The fixed corpus contains 56 cases from seven graphs,
four imported and three generated, at the eight primitive inputs. Expected
Words were computed outside Lean; native validation confirmed all 56 and
replayed 224 typed reductions. Before activation the same independent evaluator
agreed with original Core on 26 generated graphs at all eight inputs, and eight
generated cases matched on O0, O2 and Yul.

The full Lean build (9,927 jobs) and registered test driver passed. The full
Python policy suite passed 445 tests, including the process-cleanup
regressions. All 492 retained cases replayed with identical complete JSON and
Core observations; the other seven native tools kept their hashes.

All 56 fixed cases matched on O0, O2 and Yul with complete feature, input,
helper and composition-shape coverage, in 340.678, 344.691 and 517.510 seconds
locally. Random seed `20261026`, sixteen cases and 2,048 attempts accepted two
graphs from fifteen attempts, with thirteen ordinary exclusions and no resource
exclusions. O0 and Yul matched all sixteen. O2 matched eight and recorded eight
compiler crashes, all inputs of one graph, with the same host integer-conversion
panic recorded for the primitive and call-graph families; automatic reduction
retained the crash fingerprint. That O2 random gate failed. Per the user's
instruction, the symptom is recorded without upstream investigation or a
backend patch.

A two-helper fixed case passed controlled synthetic reduction on each backend:
twelve accepted typed reductions kept every helper and binder. Original and
final archives replayed exactly with three-way agreement (six replays),
synthetic fingerprints reproduced and fuel-one executions were inconclusive.
Suite totals are now 571 fixed cases/scenarios for Sonatina and 535 pure cases
for Yul. Hosted CI still has not been run.

The three planned priority-4 families are now connected. Private-cell effects in
the direct grammar and unrestricted recursion remain outside these profiles.
The next priority is the minimal Rust-dialect emitter proof below.

**Minimal emitter proof:** begin with the actual emitted Word/Bool fragment,
fresh local bindings and conditionals. Define the relevant Rust-dialect source
meaning independently and connect the real emitter and wrapper to it. State
the parsing/typing boundary and any remaining compiler assumptions. A proof
about native Lean frontend syntax, or Core typing alone, is not this result.

The minimal theorem is kernel-checked; [scalar emitter meaning](scalar-emitter-meaning.md)
states it and its boundary. `emit_source_meaning` and
`Input.emit_source_meaning` start from a successful actual emission. They lex
and parse the emitted `String`, then call `run()` or `run(uint256)` under an
independent source semantics. The returned word equals the Word that Core's
`runStateful` returns for the original program, or for the original lambda at
every input. The semantics gives `word` operators the EVM instructions selected
by the pinned standard library, and models lexical scopes, typed `let`,
assignment and `if`. `render_spec` unfolds the actual `ScalarRenderer.render`;
no substitute printer or native frontend syntax is involved. The proofs use only
Lean's standard axioms, and the semantic-kernel policy now covers them.

The remaining Rust pipeline is assumed, not proved: parsing the text as the
modeled grammar, name resolution and typing, the transcribed standard-library
meaning, lowering, backend compilation, EVM execution and ABI dispatch.
Differential tests still provide the only evidence for those steps. Helper
calls, raw primitive aliases and the aggregate, loop, mutation, storage, call,
closure, generic, comptime and module emitters are not covered.

The registered `SourceScalarMeaning` test runs actual emitted texts through
the same lexer, parser and semantics. Fifteen closed fixtures, twelve input
fixtures at eight boundary inputs and twenty generated programs agree with
Core; malformed and meaningless texts are rejected. The full Lean build (9,939
jobs), registered tests and the semantic-kernel policy passed.

**State and ABI:** expand from the existing two-slot, Word-input and bounded
call profiles to selected dynamic ABI values and richer account/storage or
transaction behaviors. Define committed observations, rollback, deployment and
sequence reduction before enabling each feature. Gas-sensitive equivalence,
precompiles and arbitrary external accounts require separate explicit scopes.

The first extension, `stateful-keyed-storage`, is connected to the native case
tool, the storage adapter and campaign, and the suite as an eighteenth profile.
Its definitions were fixed before execution:

- Transactions: one to three zero-value calls of `run(uint256 key, uint256
  input)` with exactly two ABI Words; malformed calldata is outside the scope.
- Effects: write the key slot, its wrapping successor, then counter slot zero,
  so later writes win when keys alias the counter or each other; reread all
  three. Odd inputs revert with the tentative sum after the writes.
- Committed observations: status, payload and the committed values of the
  declared slots (counter, keys and successors, derived from the transactions)
  after every transaction on all three paths. Because Core account storage is
  not enumerable, the Hull and EVM paths additionally must show no nonzero
  committed slot outside the declaration (committed entries and Anvil's
  prestate diffs reread at each receipt block).
- Rollback: a revert keeps the prior committed snapshot on every path, chosen
  by `ContractRuntime` for original Core.
- Deployment: empty constructor and zero value; every declared slot is zero and
  no undeclared slot is nonzero afterwards. Original Core starts from the
  declared post-deployment world.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, and bank replacements of one input or key, ordered by transaction count,
  program complexity and the sum of keys and inputs. Candidates rederive their
  slots; a candidate that no longer declares a finding's slot cannot keep it.

Original Core uses the checked `wordOutcomeV1` contract convention; the
emitter, observer, Hull runner and campaign rules are separate versioned
modules, and existing schemas, saved cases and native tool hashes are
unchanged. Generation reuses the aggregate step generator and draws keys from
a six-entry bank, parity-adjusted inputs and one of four completion patterns
from a separate high-bit stream. The fixed corpus has twelve scenarios (eight
imported, four generated) and 33 transactions. Its histories were computed
outside Lean by a separate evaluator and protocol model; a registered Lean
validator confirmed every status, payload and declared slot against original
Core and rejected tampered entries. Coverage includes 21 step features, six
inputs, six keys, one to three helpers and transactions, four templates, six
completion patterns and four static alias kinds.

The full Lean build (9,934 jobs), registered tests, semantic-kernel policy and
the full Python policy suite (462 tests) passed. The fixed suite matched all 12
scenarios and 33 prefixes on Sonatina O0 and O2 (69.7 and 69.6 seconds). Random
seed `20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios
from 196 attempts, with 180 ordinary exclusions and no resource exclusions; all
sixteen and 48 prefixes matched on both levels (92.5 and 92.4 seconds), with
no finding. A copied Hull slot difference reduced a three-transaction alias
scenario to one transaction on each level (eight accepted reductions in ten
actual candidate executions); original and reduced archives replayed exactly
with agreement (four replays) and synthetic fingerprints reproduced. Core or
Hull fuel one was inconclusive. The two-slot storage and rollback profiles
still matched all 22 fixed scenarios on both levels. Yul remains restricted to
pure profiles. Hosted CI has not been run.

This scope does not compare gas, balances, nonces, logs or code, multiple
callers, nonzero call value or hashed mapping layouts. Agreement is test
evidence, not a preservation proof.

The second extension, `stateful-dynamic-array`, adds one bounded dynamic ABI
value and is connected as a nineteenth suite profile. Its definitions:

- Transactions: one to three zero-value calls of `run(uint256 flags,
  uint256[] values)` with zero to three elements in the canonical head/tail
  encoding. Non-canonical offsets and truncated arrays are outside the scope;
  there the Rust decoder reverts while Core reads absent Words as zero.
- Effects: original Core follows the head offset to the length, as the ABI
  does, and the source reads a lazily decoded calldata array. Each present
  element is folded through the checked step and written to its own slot; the
  accumulator, then a running element count, are written last. Odd flags revert.
- Committed observations, rollback and deployment: as for keyed storage, with
  the fixed declared slots zero to four and Hull/EVM containment through the
  same declared-slot Hull runner.
- Sequence reduction: step reduction, transaction removal, removal of one array
  element and bank replacement of one element or the flags, ordered by
  transaction count, program complexity, element count and value weight.

Its fixed corpus has twelve scenarios and 33 transactions whose independently
computed histories match original Core; generated calldata matched Foundry's
`cast calldata` encoder. The keyed-only adapter rules became declared-slot
rules with a per-profile ABI form. The full Lean build (9,941 jobs), registered
tests, kernel policy and 468 Python policy tests passed, and the ten earlier
native tools kept their hashes. On O0 and O2 the fixed suite matched all 12
scenarios and 33 prefixes (94.7 and 94.1 seconds). Random seed `20261026`,
sixteen cases and 2,048 attempts accepted sixteen scenarios from 195 attempts
with 179 ordinary exclusions and no resource exclusions; all sixteen and 48
prefixes matched on both levels, with no finding. A copied Hull slot difference
reduced to one transaction with an empty array on each level (twelve accepted
reductions in sixteen actual candidate executions); four exact archive replays
agreed and synthetic fingerprints reproduced. Core or Hull fuel one was
inconclusive. With the generalized adapter, the keyed fixed and random suites
and the two-slot storage and rollback fixed corpora matched again on both
levels. Hosted CI has not been run.

Further state/ABI work, such as nested or multi-word ABI elements, `bytes`,
ABI-encoded return values, multiple callers, nonzero call value or logs, needs
its own observation, rollback, deployment and reduction definitions first.
Gas-sensitive equivalence, precompiles and arbitrary external accounts keep
their separate explicit scopes.

**Native Source goal two:** follow the remaining work in
[Core runtime unification](core-runtime-unification.md#remaining-work-for-the-second-goal).
Use the actual checker-derived cached-body validity, remove the restrictive
body-profile premise through general accepted-body simulation, and compose
specialization/evidence/staging/lowering with initialization and public calls.
Do not resume disconnected small lemmas in place of that public connection.

The first step closes the existing mixed-cell statement flows by induction over
the actual accepted compiler tree of any named or contextual body invocation,
and composes the result with the actual function footer
(`CellAwareInvocationAcceptedFlow.body_preserves` and `body_reflects`). Covered
branches are returns, final values, discards, transfers, blocks, conditionals,
`while` and `for` loops, monomorphic declarations, generalized declarations with
direct lambda initializers, and bare and projected assignments, bit-not updates
and matches of named-row bodies. At an actual
prepared named header, checker certification and the cached body's Core typing
discharge the static premises (`CellAwareInvocationAcceptedNamedHeaders.static_inputs`).
Accepted-expression meaning is still a premise, contextual-view writes and
matches are not yet closed, and the public session does not yet use these
theorems. The design document lists the remaining
premises.

**Hull connections:** preserve the exact existing
[public theorem boundaries](hull-meaning-preservation.md). Connect precompile
dispatch, creation/deployment, independent assembly and source revert, then
object linking through real implementations and public consumers. Executable
coverage and differential agreement do not discharge these proof obligations.

Precompile dispatch is connected for the identity, SHA-256 and RIPEMD-160
precompiles. Their independent rules cover the gas charges, the byte copy of
the input, digests specified from FIPS 180-4 and from the RIPEMD-160
definition, failure on insufficient forwarded gas and the memory fault. They extend account dispatch, so the public theorems for
child-free calls, compiled and nested children, call modes and root reentry
now cover these precompiles without statement changes. The proof reaches the
actual dispatcher, precompile wrapper, copy loop and shared block helper;
`rfl`-checked restatements expose the builders that the implementation keeps
private. Ten independent source derivations reach the child-free and
call-mode public resumption theorems, including CALLCODE, DELEGATECALL and
SHA-256 and RIPEMD-160 digests of "abc"; runtime checks compare bytes, balances
and retained snapshots. ECRECOVER and P256VERIFY are not connected: an
independent affine specification would need field arithmetic, identities for
every Jacobian formula and ladder correctness, which do not fit in one
connected unit without an algebra library. Creation has no connected first
step yet: even its early refusals need a call-mode source rule, `supported`
entries, a create-handler closure correspondence and the actual creation
transport and dispatcher prefix. Creation/deployment, assembly and source revert, and object linking
also remain, in that order.

## Handoff rules

Use separate commits for a coherent operational change and its validation.
Keep `questions.md` ignored and uncommitted; put confirmed regressions and
public limitations in tracked tests and documentation. Update this roadmap
when a gate is actually complete, with the commands and observed results.
Delete disposable exports and validation caches once their evidence is saved.
