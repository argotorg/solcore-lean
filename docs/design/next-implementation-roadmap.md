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
| 5 | A minimal proof for the actual Rust-dialect emitter | Closed, runtime-input, named-helper, raw-primitive, call-graph, private-mutation, aggregate, aggregate call-graph, call-graph loop, aggregate loop, generic, two-slot storage, two-slot rollback and keyed-storage emitters proved locally; other emitters open | A small connected meaning-preservation theorem for what is actually emitted, not for a substitute native Lean syntax. |
| 6 | State and ABI extensions | Keyed-storage, bounded dynamic-array, event-log, call-value, bounded-`bytes`, contract-forwarded value, Keccak-addressed mapping, sender-keyed ledger and 256-byte `bytes` extensions validated locally; multi-word return values need a contract runtime change; O2 random log and forwarded-value runs have recorded compiler crashes; hosted run pending | Explicit additional observations and transaction semantics, with actual three-way tests and sequence reduction. |
| 7 | Native Source goal two | In progress: statement closure over the actual compiler tree, a first expression subset and statement shape for named rows, their public-root connection, one concrete instance, direct calls at expression roots closed by one size induction over a family of rows, call authority from a complete inventory, and the public root's preservation direction for call-containing rows; root reflection, lifting of call-containing bodies, a one-call instance, nested calls, remaining expression and statement forms, fault lifting, a richer instance and chained public calls remain | Complete accepted-body preservation and connect all actual passes to the public session. |
| 8 | Remaining Hull public connections | In progress: identity, SHA-256 and RIPEMD-160 precompiles, refused CREATE/CREATE2 attempts, admitted attempts without an init frame, Hull's explicit revert and inline Yul statement lists with locals, assignments, nested blocks, `if`, `switch`, nested memory and termination calls and the word operations `add`, `sub`, `lt`, `gt`, `eq` and `iszero` connected | Independent semantics through actual lowering, initialization and public execution for each remaining feature. |

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

The same raw primitives now render in the eleven profiles whose step functions
use `AggregateRenderer` (aggregates, loops, generics, closures, comptime and
module steps, storage, rollback, calls, keyed storage and dynamic arrays). The
renderer reuses the call-graph helpers, snapshots, reversed shift arguments and
alias spellings; programs without a primitive emit byte-identical source, and
the aliases are imported only when used. Emitter and profile versions moved to
`v2`; the 202 legacy cases of the six affected pure profiles are rejected by the
version check and the other 347 replay identically. In the recorded random
allocation, operator exclusions fell from 42/23/33/47/376/574/206/206/149/180/163
to zero, except 17 comptime and 9 module exclusions from their scalar constants.
Each affected corpus gained entries covering all fourteen primitive features.
`ScalarRenderer`, `MutationRenderer` and template-budget exclusions are
unchanged. Fixed suites matched all 256 pure cases on O0, O2 and Yul and all 71
stateful scenarios on O0 and O2; random seed `20261026` matched all 96 pure
cases on the three backends and all 80 stateful scenarios on O0. On O2 the
stateful random suite failed: one dynamic-array scenario, which matched on O0,
crashed code-image export with the Q013 panic, and reduction kept a large
constant left shift. The finding is retained; hosted CI has not been run.

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
Differential tests still provide the only evidence for those steps.

The proof now also covers the `runtime-functions` emitter.
`Function.emit_source_meaning` states that its text parses to one free function
per Core helper and that `run(uint256)` returns the Word of the original Core
binding chain at every input. Each source helper sees only earlier helpers, as
Core closures capture only earlier helpers.

The `runtime-primitives` emitter is covered as well.
`Primitive.emit_source_meaning` gives the fourteen raw `std.opcodes` aliases the
EVM instructions they import, and proves that each Core Word operation agrees
with its instruction. These include signed division and remainder, the
arithmetic shift, sign extension, exponentiation, `CLZ` and the untruncated
modular operations. The renderer lemmas are now generic over how a renderer
prints each constructor and over the call context, so the primitive renderer
reuses the shared cases.

`CallGraph.emit_source_meaning` covers the `runtime-call-graphs` emitter, whose
helpers and entry may call earlier helpers and the raw opcode aliases. The
helper loop proof is now generic over the renderer and the call context, and
helper names never shadow an alias.

`Mutation.emit_source_meaning` covers the `runtime-mutation` emitter, whose
private mutable Word locals live in the Core store. Each source `sc_c<n>` local
holds the Word of its Core cell, every read is copied before a later write, and
helpers keep their caller's store. Because such a program ends with its cells
in the store, the result is stated for some final store that every completed
run reaches.

`Aggregate.emit_source_meaning` covers the `runtime-aggregates` emitter with
the same store-aware statement. The source grammar and semantics now include
`(word, word)` pairs, `sum<word, word>` with `inl` and `inr`, the pair match
printed for projections and the sum match with a payload in each case scope.
A match evaluates its scrutinee once. Pairs, `sum`, `inl` and `inr` are
frontend builtins, whose assumed meaning cites the pinned name resolver. The
proof relates Core pairs and sums to source pairs and tagged sums, binds each
Core `case` payload in the selected case scope under a fresh name, and extends
the mutation invariant for cells, helper calls and raw opcode operands. The
file imports the raw aliases only when a rendered body uses one, and the proof
needs the alias call context only for such bodies.

`AggregateCallGraph.emit_source_meaning` covers the
`runtime-aggregate-call-graphs` emitter, whose helpers and entry compose Word
pairs, sums, projections and case payloads with calls to earlier helpers and
the raw opcode aliases. Its text needs no new source form. The proof maps the
renderer's Word, Boolean, pair and sum bindings to aggregate bindings and
reuses the aggregate invariant and lemmas; as in the call-graph emitter, the
file always imports the aliases. The renderer refuses cells and the
executable checks observe an empty final Core store, but the theorem keeps the
store-aware statement.

`CallGraphLoop.emit_source_meaning` covers the `runtime-call-graph-loops`
emitter, whose method applies a scalar call-graph step `input & mask` times in
a source `while` loop. The loop has its own grammar and fuel-indexed meaning,
next to the loop-free ones: `parseLoopSource` also reads
`while (a op b) { ... }` at the top level of a method body, and
`loopSourceCall fuel` lets each loop evaluate its condition at most `fuel`
times. More fuel never changes a result, and on every text that `parseSource`
accepts, `loopSourceCall` equals `sourceCall`, so no existing statement
changed. The theorem states that every fuel above the mask returns the Word
that Core's bounded-loop reference returns, with its final store. The proof
prints the entry as one more helper, `sc_step`, and relates Core's ordinal
guards, restated from a private definition, to the counting loop by induction.
The step is pure in Core, so the proof tracks only the accumulator cell, which
the executable checks observe as the final store.

`Loop.emit_source_meaning` covers the `runtime-loops` emitter, which prints the
same wrapper around an aggregate step. Its text needs no new source form, so
the loop grammar and meaning are reused unchanged. The step comes from the
aggregate renderer and may allocate private cells, which Core keeps in its
store; the store therefore grows across iterations. The aggregate helper
relation states that each call keeps every existing location, so the induction
over the guards carries a growing store in which the accumulator stays in the
first cell. The theorem is stated with the final store, which the executable
checks observe as the accumulator cell followed by the step's cells.

`Generic.emit_source_meaning` covers the `runtime-generics` emitter. Its file
declares the generic selector `sc_select<a>` before the aggregate helpers and
the step, and its method applies the step to the input and to the input plus
one, then selects between the results by the input's low bit at `word`,
`(word, word)` or `sum<word, word>`. The text needs three forms outside the
loop-free fragment: a generic function with a type parameter, an `if` without
`else` that returns early, and a `let` or assignment with one infix operation
without parentheses. They have their own grammar and meaning, next to the
loop-free and loop ones: `parseGenericSource` also reads generic functions,
guards and infix statements, and `genericSourceCall` lets a type parameter
admit every value, so its consistent instantiation is part of the assumed
frontend typing. On the printing of every loop-free file with valid,
non-reserved names, `genericSourceCall` equals `sourceCall`, so no existing
statement changed. The theorem states that the method returns the Word that
Core's generic reference returns, with its final store. That reference applies
a monomorphic curried selector closure; the proof restates it and the applied
entry from private definitions for each variant. A call resolves to the
selector only because no helper is named `sc_select`, which a named copy of the
aggregate helper-loop lemma states; the original lemma is unchanged. The step
may allocate private cells, so the final store holds the cells of both step
calls.

`Storage.emit_source_meaning` covers the `stateful-storage` emitter, whose
method reads two storage slots, stores the step's result for the input plus
slot 0 in slot 0 and slot 1 plus one in slot 1, and returns the sum of both
slots read back. It is the first theorem with a stateful source semantics. The
storage grammar and meaning are separate from the others: `parseStorageSource`
also reads the `sload, sstore` import line, `sstore(slot, value);`, a `let`
whose call argument is one infix operation and an infix operation in the
returned `uint256(...)`. `storageSourceCall` runs the method from a storage
and returns its word with the final storage; `sload` reads the current storage
and free functions see none. The Core reference is a host-runtime contract.
The theorem therefore observes one top-level transaction, the runner of the
storage differential oracle, on any world in which the contract is installed,
with calldata whose word at offset 4 is the input. The source call starts from
the installed account's storage. With enough fuel the transaction completes,
and every completed run returns the ABI encoding of the source's word and
commits an account whose storage equals the source's final storage at every
slot. Because the starting storage is arbitrary, the statement applies to each
transaction of a history. The proof builds the host-machine path through the
wrapper's seven requests with the existing handled-path, big-step and
read-after-write lemmas; no existing statement changed. The new assumptions
are the parsing of the import selection, call statements and infix call
arguments, the resolution of `sload` and `sstore` to the `std.opcodes`
wrappers, their `SLOAD` and `SSTORE` meaning, and storage lowering and ABI
dispatch.

`StorageRollback.emit_source_meaning` covers the `stateful-storage-rollback`
emitter and both of its outcomes. Its method runs the storage protocol and binds
the sum of both slots read back. For an odd input it stores the sum at memory
offset 0 and reverts with those 32 bytes; otherwise it returns the sum. The
rollback grammar extends the storage grammar with an operation `let` and the
terminal revert block `if (a op b) { mstore(o, v); revert_(o, 32); }`. In the
rollback meaning a call returns its word with the final storage, or reverts
with a word and keeps none of its storage writes. A revert that reads other
memory has no meaning. The theorem states that the source call reverts exactly
when the input is odd, and that the Core transaction settles as the source
outcome. A returned call returns the same ABI bytes and commits the same
storage. A reverted one reverts with the 32-byte encoding of the same word and
commits the world the transaction started from, so the installed account keeps
its storage. The proof reuses the storage path, extended by the Core
completion that selects the outcome profile's tag, and adds a top-level lemma
for the reverted outcome; no existing statement changed. The new assumptions
are the parsing of the `if` without `else`, the call statements and the
operation `let`, and the `MSTORE` and `REVERT` meaning of the wrappers. They
also include that a reverting call discards its storage writes.

`KeyedStorage.emit_source_meaning` covers the `stateful-keyed-storage` emitter.
Its method takes a key and an input and writes the key slot, the key's wrapping
successor and counter slot zero in the original Core contract's order. It then
reads all three back and reverts with their sum for an odd input, otherwise
returning it. Computed slots need no new source form, since `sload` and
`sstore` take any word. The keyed grammar extends the rollback one only by the
left-folded sum `let x: T = a + b + c;`. The theorem is the rollback statement
for two calldata words, at offsets 4 and 36, and covers every key. That
includes zero and `2^256 - 1`, whose writes alias the counter. One agreement
lemma for single writes carries the source and Core storage through the
writes in order, so aliasing needs no case analysis. The new assumptions are
the left association of `+`, the dispatch of two arguments and that `SLOAD` and
`SSTORE` address computed slots. The other emitters that render with the
aggregate renderer (closures, comptime, modules, storage mappings,
sender-keyed ledgers, dynamic arrays, dynamic bytes, long bytes, event logs,
call value, calls and forwarded value) are not covered; their texts use forms
outside the source fragments.

The registered `SourceScalarMeaning` test runs actual emitted texts through
the same lexer, parser and semantics. Fifteen closed fixtures, twelve input
fixtures, four named-helper graphs, 39 raw primitive bodies, twenty call graphs
and six mutation graphs at eight or more boundary inputs, and twenty generated
programs, agree with Core. Fifty-four primitive and call-graph results and the
mutation results also match hand-known Words. Malformed and meaningless texts,
including calls to aliases that are not imported, are rejected. The registered
`SourceAggregateMeaning` test runs six aggregate regression graphs, ten `if`
and `case` joins over every target, four templates, eighteen raw primitive
bodies and 24 generated aggregate graphs at eight boundary inputs; all agree
with Core, and the regression graphs, joins and templates also match
hand-known formulas. Malformed aggregate texts, such as a payload used after
its case or a primitive text without its alias import, are rejected. The
registered `SourceAggregateCallGraphMeaning` test runs the regression graph
with all nine composition shapes, twelve shape graphs, three helper-call
graphs, 28 raw primitive bodies inside pairs and sums and 24 generated graphs
at eight boundary inputs; all agree with Core, every Core run ends with an
empty store, and the fixed graphs also match hand-known results. A helper
applied to a pair or returning one, a helper that calls a later helper and a
primitive text without its import line are rejected. The registered
`SourceCallGraphLoopMeaning` test runs two closed-form plans, the identity step
under every admitted mask, two mixed call-graph plans, fourteen raw primitive
steps and 24 generated plans at eleven or more inputs. Each call agrees with
Core at one more unit of fuel than its iterations and has no meaning with less,
and every Core run ends with the one accumulator cell. Loop-free texts keep
their `sourceCall` meaning, and altered loops lose or change their meaning. The
registered `SourceLoopMeaning` test runs eight fixed aggregate steps, including
one that allocates a cell per call, under every admitted mask, fourteen raw
primitive steps and 23 generated plans with the same fuel checks. Every Core
run ends with the accumulator cell followed by the step's cells, and the fixed
steps also match hand-known formulas and cell counts. The registered
`SourceGenericMeaning` test runs seven regression plans, including a step that
allocates a cell per call, fourteen raw primitive steps at each variant and 22
generated plans at eight or more inputs. All agree with Core, the regression
plans also match hand-known Words and cell counts, and every Core run ends with
Word cells only. Loop-free texts keep their `sourceCall` meaning, altered
selectors lose or change their meaning, and two infix operations without
parentheses are rejected. The registered `SourceStorageMeaning` test runs six
regression plans, fourteen raw primitive steps and 23 generated scenarios
through histories from empty and from two nonempty storages. Each of the 627
transactions starts from the committed account's storage and agrees with the
Core transaction on its word, its ABI bytes and the committed slots, and the
regression plans also follow the two-slot recurrence. Altered stores and loads
change the result, and a free function that reads storage has no meaning. The
registered `SourceRollbackMeaning` test runs six regression plans, fourteen raw
primitive steps and 23 generated scenarios through the same kind of histories.
Their 675 transactions, 363 returned and 312 reverted, settle as Core. Odd
inputs revert with the recurrence's sum and keep every compared slot, even
inputs return and commit their slots, and altered revert blocks lose or change
their meaning. The registered `SourceKeyedMeaning` test runs the four golden
histories, five regression plans, fourteen raw primitive steps and 22
generated scenarios with aliasing keys. All 674 transactions settle as Core,
and reordered writes change the result for the aliasing key zero but not for
key one. The full Lean
build (10,110 jobs), registered tests and the semantic-kernel policy
passed.

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

The third extension, `stateful-logs`, makes event logs committed observations.
Its definitions were fixed before execution:

- Transactions: one to three zero-value calls of `run(uint256 flags, uint256
  input)` with exactly two ABI Words; malformed calldata is outside the scope.
- Effects: write `step(input + slot0)` to slot zero and a counter to slot one.
  Up to three static log sites follow, each guarded by one flags bit and
  emitting LOG0 to LOG4 with zero, one or two data Words. Topics and data are
  derived from a further step application. Odd flags revert after every write
  and log.
- Log observation: for each transaction, the ordered list of committed logs,
  each with its emitter address, topics and data bytes, on all three paths.
  Core's host offers only the one-topic, one-Word `emitLogWord`, so the Core
  contract writes each site as a fixed frame of word logs and a versioned
  observer decodes the committed journal; Core itself is unchanged. Hull uses
  its receipt logs; the EVM path uses each mined receipt's logs.
- Rollback: a reverted transaction has no logs and keeps the prior committed
  slots on every path. Logs committed earlier stay: after the sequence, the EVM
  chain's complete log list for the contract must equal the concatenation of
  the committed receipts' logs. Core and Hull histories only append.
- Deployment: no constructor and no constructor logs. Hull and EVM deployment
  receipts must contain no logs and leave every slot zero; original Core starts
  from the declared post-deployment world with no logs.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, log-site removal or simplification (dropping a site's last topic or
  data Word), and input simplification (a bank input, one of flags bits zero
  to three cleared, or only those four bits kept), ordered by transaction
  count, program complexity and the sum of flags and inputs.

Core and its host interface are unchanged: the Core contract writes each site
as a frame of `emitLogWord` records under `core-word-log-framing-v1`, and the
observer decodes the public runtime's committed journal, treating a malformed
frame as an observer failure. The source calls the pinned `std.opcodes`
wrappers `log0` to `log4`. The declared-slot Hull runner already exported the
logs of each receipt and serves this profile unchanged. The profile is a
twentieth suite profile with a twelfth native tool, `semantic-log-tool`; the
eleven other native tools kept their hashes. Generation reserves the measured
wrapper of one to three sites before generating the step. Sites, guards,
inputs, guard masks, high flags bits and the completion pattern come from a
separate high-bit stream. 283 of the first 300 seeds at 384 nodes were
accepted.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions that commit 27 logs. Its histories were computed outside Lean by
a separate evaluator of the step programs and a direct model of the protocol.
A registered Lean validator confirmed every status, payload, slot and log
against original Core and rejected tampered entries. Coverage includes all 39
step features of the corpus, six inputs, one to three helpers and
transactions, four templates and six completion patterns. It also includes
committed log counts zero to three, topic arities zero to four, data lengths
of 0, 32 and 64 bytes, and reverted transactions discarding zero to three
guarded sites.

The full Lean build (9,995 jobs), registered tests, kernel policy and 482
Python policy tests passed. The fixed suite matched all 12 scenarios and 33
prefixes on Sonatina O0 and O2 (68.3 and 68.1 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
eighteen attempts, with two ordinary exclusions and no resource exclusions.
O0 matched all sixteen and 48 prefixes (92.7 seconds), covering every log
count, topic arity and data length. O2 matched fifteen and 45 prefixes. Its
remaining scenario crashed the compiler during O2 code-image export with a
host `arithmetic operation overflow` panic in `primitive-types`, a different
message from the earlier shift-count panic. Checked Hull export succeeded, and
the same scenario matched on O0. That O2 random gate failed. Per the user's
instruction, the symptom is recorded in the local `questions.md` without
upstream investigation. The attempt-limited automatic reduction kept the
crash fingerprint.

A copied Hull log difference at the last of three transactions was reduced on
each level to that transaction with one site and one data Word: twelve
accepted reductions in 28 actual candidate executions. Original and reduced
archives replayed exactly with agreement (four replays), and synthetic
fingerprints reproduced. Core or Hull fuel one was inconclusive. With the
extended adapter, the storage, rollback, call, keyed and dynamic-array fixed
corpora still matched all 71 scenarios and 197 prefixes on both levels. An
offline preparation of the worktree's cloned cache then verified all twelve
native tools as ready. Hosted CI has not been run.

This scope does not compare gas, balances, nonces or code, constructor logs,
logs from more than one contract, data lengths other than whole Words, or ABI
event signatures. Agreement is test evidence, not a preservation proof.

The fourth extension, `stateful-call-value`, adds nonzero call value with the
contract's own balance as a committed observation. Its definitions were fixed
before execution:

- Transactions: one to three calls of the payable `run(uint256 flags, uint256
  input)` with exactly two ABI Words and a call value of 0, 1, 7, 2^64 - 1,
  2^64 or 2^70. A scenario sends at most 2^72 in total, which the funded local
  sender can always pay. Malformed calldata is outside the scope.
- Effects: compute `step(input + callvalue + slot0)` into slot zero and add
  the call value to slot one. Odd flags revert after both writes.
- Committed observations: status, payload, slots zero and one, and the
  contract's committed balance after every transaction on all three paths,
  with the keyed profile's containment of other slots on the Hull and EVM
  paths. The sender's balance is never observed, because EVM gas changes it.
  Every committed balance must equal the deployment value plus slot one.
- Rollback: a reverted transaction refunds its value. The contract keeps its
  prior committed balance and slots on every path. Original Core's balanced
  root runs on the post-transfer world with the pre-transfer world as its
  checkpoint.
- Deployment: an empty payable constructor deployed with a recorded value of
  zero or five. Every path starts with that balance, zero slots and no
  constructor logs; original Core starts from the declared post-deployment
  world.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, a bank input, a smaller bank value, flags reduced to their parity or
  with the revert bit cleared, and a zero deployment value, ordered by
  transaction count, program complexity and the sum of flags, inputs, values
  and the deployment value.

Original Core runs each transaction through `BalancedTopLevelExecution`. It
transfers the value before the root runs and refunds it through the checkpoint
world on revert; Core and its host interface are unchanged. The source reads
`callvalue` through the pinned `std.opcodes` wrapper in a payable method,
behind a payable constructor. The keyed-storage Hull runner rejects nonzero
value, so a new runner, `rust-hull-value-scenario`, performs each top-level
transfer in its checked ledger. The EVM path deploys and calls with value and
reads `eth_getBalance` at each receipt block. The profile is a twenty-first
suite profile with two new native tools; the twelve other native tools kept
their hashes. Generation draws three inputs, three bank values, a deployment
value of zero or five and a completion pattern from a separate high-bit
stream. All of the first 300 seeds at 384 nodes were accepted.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions. Its histories, including every committed balance, were computed
outside Lean by a separate evaluator of the step programs and a direct model
of the protocol. A registered Lean validator confirmed every status, payload,
slot and balance against original Core and rejected tampered entries.
Coverage includes all 39 step features of the corpus, six inputs, one to
three helpers and transactions, four templates, six completion patterns, all
six bank values, refunds of 0, 1, 2^64 - 1, 2^64 and 2^70, and both
deployment values.

The full Lean build (10,017 jobs), registered tests, kernel policy and 494
Python policy tests passed. The fixed suite matched all 12 scenarios and 33
prefixes on Sonatina O0 and O2 (66.8 and 66.5 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
sixteen attempts with no exclusions. All sixteen and 48 prefixes matched on
both levels (94.9 and 93.5 seconds), refunding every bank value and covering
both deployment values and all four generated completion patterns, with no
finding.

A copied Hull balance difference at the last of three transactions was
reduced on each level to that transaction with zero flags, input, value and
deployment value: six accepted reductions in six actual candidate executions.
The first reduction run stopped at a deployment value of five, because the
campaign's candidate identity omitted the plan's deployment value. The
identity now includes it, other profiles keep theirs, and the whole matrix
was rerun on the corrected scripts. Original and reduced archives replayed
exactly with agreement (four replays), and synthetic fingerprints reproduced.
Core or Hull fuel one was inconclusive. With the extended adapter, the
storage, rollback, call, keyed, dynamic-array and log fixed corpora still
matched all 83 scenarios and 230 prefixes on both levels. An offline
preparation of the worktree's cloned cache verified all fourteen native tools
as ready. Hosted CI has not been run.

This scope does not compare the sender's balance, gas, nonces or code, value
sent by contracts, values above the local sender's funds or non-payable
methods. Agreement is test evidence, not a preservation proof.

The fifth extension, `stateful-bytes`, adds one bounded dynamic `bytes`
value. The pinned dialect decodes `bytes` without upstream changes, but only
into memory: `memory<bytes>` has an ABI decoder and the `bytes` signature
string. A probe that stored a decoded payload's length, Words and last byte
gave the expected values on Sonatina O0 and O2 and through the declared-slot
Hull runner, so the sender-dependent fallback was not needed. Its definitions
were fixed before execution:

- Transactions: one to three zero-value calls of `run(uint256 flags, bytes
  payload)` with a payload of 0 to 64 bytes, including lengths that are not
  multiples of 32, in the canonical encoding: flags, the tail offset 64, the
  length, the payload and zero padding to a whole Word. Non-canonical offsets,
  truncated or longer payloads and nonzero padding are outside the scope.
- Effects: fold each present 32-byte chunk of the payload (at most two, with
  bytes at or past the length read as zero) through the checked step from
  slot zero, writing slot `1 + k` after chunk `k`. Then write the accumulator
  to slot zero, a running byte count to slot three and the last payload byte
  (zero when empty) to slot four. The result is the sum of slots zero, three
  and four, read back, plus the calldata size. Odd flags revert with it after
  the writes.
- Reading: original Core follows the head offset with `inputDataWordBE?`,
  reads each chunk Word with it and masks the chunk to the payload length, and
  reads the last byte with `inputDataByte?` and the calldata size with
  `inputDataSize`; Core is unchanged. The source receives `memory<bytes>` and
  reads the decoder's zero-padded copy with `mload`, the last byte through an
  unaligned load of the Word that ends at it.
- Committed observations, rollback and deployment: as for the dynamic-array
  profile, with the fixed slots zero to four. Status, payload and those slots
  are compared after every transaction on all three paths, and the Hull and
  EVM paths must show no nonzero committed slot outside them. A revert keeps
  the prior committed slots, and an empty zero-value constructor leaves every
  slot zero. Every committed row must also follow the protocol: a returned
  transaction adds its payload length to slot three, leaves its last byte in
  slot four and returns the sum of the committed slots zero, three and four
  plus its calldata size.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, truncation of one payload to a shorter bank length, zeroing one
  payload's bytes, and flags reduced to their parity or with the revert bit
  cleared, ordered by transaction count, program complexity, total payload
  length, then the sum of flags and payload bytes.

Original Core reads calldata with `inputDataWordBE?`, `inputDataByte?` and
`inputDataSize`; Core and its host interface are unchanged. The source takes
the `memory<bytes>` the pinned dispatcher decodes and reads it through the
`mload` and `calldatasize` wrappers. The declared-slot Hull runner serves the
profile unchanged. The profile is a twenty-second suite profile with one new
native tool, `semantic-bytes-tool`; the fourteen other native tools kept their
hashes. Generation reserves the measured 176-node wrapper before generating
the step. Three lengths from a nine-entry bank, three byte patterns and the
completion pattern come from a separate high-bit stream, and seeded bytes
from a further stream. 275 of the first 300 seeds at 384 nodes were accepted.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions. Its histories were computed outside Lean by a separate evaluator
of the step programs and a direct model of the protocol. A registered Lean
validator confirmed every status, payload and slot against original Core and
rejected tampered entries. Generated calldata matched Foundry's `cast
calldata` encoder. Coverage includes all 39 step features of the corpus, the
six boundary Words as chunks, one to three helpers and transactions, four
templates, six completion patterns, all nine bank lengths and reverted
payloads of 0, 17, 32, 33 and 64 bytes.

The full Lean build (10,038 jobs), registered tests, kernel policy and 501
Python policy tests passed. The fixed suite matched all 12 scenarios and 33
prefixes on Sonatina O0 and O2 (73.5 and 73.4 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
eighteen attempts, with two ordinary exclusions and no resource exclusions.
All sixteen and 48 prefixes matched on both levels (101.5 and 100.5 seconds),
covering every bank length and four completion patterns, with no finding.

A copied Hull difference in slot two at the last of three transactions was
reduced on each level to that transaction with zero flags, an empty payload
and a reduced step: nine accepted reductions in nine actual candidate
executions. Original and reduced archives replayed exactly with agreement
(four replays), and synthetic fingerprints reproduced. Core or Hull fuel one
was inconclusive. With the extended adapter, the storage, rollback, call,
keyed, dynamic-array, log and call-value fixed corpora still matched all 95
scenarios and 263 prefixes on both levels. An offline preparation of the
worktree's cloned cache verified all fifteen native tools as ready. Hosted CI
has not been run.

This scope does not compare gas, balances, nonces, code or memory, payloads
longer than 64 bytes, non-canonical encodings and the decoder's revert paths,
strings, `bytes` return values or nested dynamic values. Agreement is test
evidence, not a preservation proof.

The sixth extension, `stateful-forwarded-value`, has a contract send value.
The bounded `stateful-calls` profile already forwards zero or one unit from a
fixed eight-unit parent endowment in zero-value transactions. This profile
funds the parent from the sender and forwards bank values. Core and upstream
stay unchanged: original Core's parent calls the child with
`callContractWordWithValue`, the source passes the value to the raw `call`
wrapper, and Hull already transfers nested value. Its definitions were fixed
before execution:

- Transactions: one to three calls of the payable `run(uint256 target,
  uint256 input, uint256 amount)` on the parent, each with a call value and an
  amount from the bank 0, 1, 7, 2^64 - 1, 2^64 and 2^70. The target is the
  bound child address; malformed calldata is outside the scope.
- Effects: the parent adds the input and its call value to slot zero, then
  calls the child's payable fallback with the input Word and value `amount`.
  The child computes `step(input + callvalue + slot0)` into slot zero and adds
  its call value to slot one; an odd input makes it revert with that Word after
  the writes. The parent writes the child's payload to slot one, plus one if
  the child reverted, and returns the sum of its two slots. Inputs with bit two
  set make the parent revert after those writes.
- Committed observations: root status and payload, and both contracts'
  balances and slots zero and one after every transaction on all three paths.
  Committed logs must stay empty. The sender's balance is never observed.
- Rollback and refunds: a child revert leaves the child's account unchanged,
  so the forwarded amount stays with the parent. A root revert, alone or after
  a child revert, keeps both prior accounts and returns the call value to the
  sender. Every committed state satisfies two balance rules: the child holds
  exactly its slot one, and the two balances sum to the parent's endowment plus
  every committed call value.
- Deployment: the child deploys with zero value; the parent's empty payable
  constructor receives 2^72, which covers three forwards of 2^70. Both start
  with empty storage and no logs. Original Core starts from the declared
  post-deployment world, with a caller holding 2^80.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, a bank input, clearing the child or root revert bit, and a smaller bank
  call value or amount, ordered by transaction count, program complexity, then
  the sum of inputs, call values and amounts.

Original Core runs each transaction through `BalancedTopLevelExecution` with a
registry of both contracts. A new runner, `rust-hull-forward-scenario`, funds
the caller, endows the parent and performs each top-level transfer in its
checked ledger; the fixed eight-unit call runner is unchanged. The call
differential and campaign gained a profile table, and `stateful-calls` keeps
its schemas, rules and fixed corpus. The profile is a twenty-third suite
profile with two new native tools; the fifteen other native tools kept their
hashes. Generation reserves the measured 169-node wrappers before generating
the step. Three bank inputs, their call modes, three call values and three
amounts come from a separate high-bit stream. 275 of the first 300 seeds at
384 nodes were accepted.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions. Its histories, including both balances after every
transaction, were computed outside Lean by a separate evaluator of the step
programs and a direct model of the protocol. A registered Lean validator
confirmed every status, payload, account and empty log list against original
Core and rejected tampered entries. Coverage includes all 39 step features of
the corpus, the ten boundary inputs, all four call modes, one to three
helpers and transactions, four templates and every bank value as a call value
and as an amount. It also covers forwards of 1, 2^64 and 2^70 that child
reverts kept with the parent, and call values of 0, 7, 2^64 - 1 and 2^70 that
root reverts returned.

The full Lean build (10,050 jobs), registered tests, kernel policy and 507
Python policy tests passed. The fixed suite matched all 12 scenarios and 33
prefixes on Sonatina O0 and O2 (71.2 and 77.4 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
seventeen attempts, with one ordinary exclusion and no resource exclusions.
O0 matched all sixteen and 48 prefixes (98.1 seconds), with child-revert and
root-revert refunds of every bank value and all four call modes. O2 matched
fourteen and 42 prefixes. Its other two scenarios crashed the compiler during
O2 code-image export with the shift-count panic `Integer overflow when
casting to usize` recorded for Q013. Checked Hull export succeeded, and the
same scenarios matched on O0. That O2 random gate failed. Per the user's
instruction, the symptom is recorded in the local `questions.md` without
upstream investigation, and the findings are retained.

A copied Hull child-balance difference at the last of three transactions was
reduced on each level to that transaction with zero input, call value and
amount and a reduced step: nine accepted reductions in nine actual candidate
executions. Original and reduced archives replayed exactly with agreement
(four replays), and synthetic fingerprints reproduced. Core or Hull fuel one
was inconclusive. With the extended call and suite scripts, the storage,
rollback, call, keyed, dynamic-array, log, call-value and bytes fixed corpora
still matched all 107 scenarios and 296 prefixes on both levels. An offline
preparation of the worktree's cloned cache verified all seventeen native
tools as ready. Hosted CI has not been run.

This scope does not compare the sender's balance, gas, nonces or code,
forwards the parent cannot pay, value sent by the child, deeper or repeated
calls, or logs. Agreement is test evidence, not a preservation proof.

The seventh extension, `stateful-mapping`, addresses storage through a
mapping, whose entries live at Keccak-256 slots. The pinned std derives the
slot of `m[k]` as `keccak256(p ++ k)`, the field's base slot followed by the
key, both as big-endian Words. That is the reverse of Solidity's
`keccak256(k ++ p)`, although the std comment cites Solidity's layout. A
probe confirmed this order on Sonatina O0 and O2; the profile follows the
pinned dialect. Original Core needs no Core or host change. It hashes with the
Core Keccak-f[1600] permutation and digest builders that the Hull import path
already uses for the `keccak256` builtin, converted to Wire with
`Wire.Expr.ofCore?`; a probe of two Words matched `cast keccak` on four
vectors. The reference stays trustworthy although it shares these builders
with the Hull path. Both builders are proved against the independent
`KeccakSemantics` specification (`permute_evaluates`, `digest_evaluates`),
the EVM path computes Keccak in the EVM itself, and the fixed corpus's slots
and histories come from Foundry's `cast keccak`. Only the 64-byte absorption
of two Words is new, and tests check it against `cast keccak` vectors. Its
definitions were fixed before execution:

- Transactions: one to three zero-value calls of `run(uint256 flags, uint256
  key, uint256 input)` with exactly three ABI Words on a contract with a
  `counter: word` field at slot zero and an `entries: mapping(word => word)`
  field at base slot one, the dialect's form of `mapping(uint256 =>
  uint256)`. Malformed calldata is outside the scope.
- Effects: read `old = entries[key]`, write `entries[key] = step(input +
  old)` and then `entries[key + 1] = old + 1` (the key wraps), and increment
  the counter. The result rereads `entries[key] + entries[key + 1] + counter`.
  Odd flags revert with it after the writes.
- Committed observations: status, payload and the committed values of the
  declared slots after every transaction on all three paths. The declared
  slots are the counter slot and `keccak256(1 ++ k)` and `keccak256(1 ++ (k +
  1))` for every transaction key `k`, derived from the transactions. As for
  keyed storage, the Hull and EVM paths must show no nonzero committed slot
  outside the declaration, so a wrong slot derivation is a difference even
  where the values agree.
- Rollback: a revert keeps the prior committed snapshot on every path, chosen
  by `ContractRuntime` for original Core.
- Deployment: empty constructor and zero value; every declared slot is zero
  and no undeclared slot is nonzero afterwards. Original Core starts from the
  declared post-deployment world.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, a bank key or input, and flags reduced to their parity or with the
  revert bit cleared, ordered by transaction count, program complexity, then
  the sum of flags, keys and inputs. Candidates rederive their declared slots;
  a candidate that no longer declares a finding's slot cannot keep it.

Original Core hashes with the Keccak closure that `Wire.Expr.ofCore?` converts
from the proved builders, 2,654 Wire nodes outside the step budget, and needs
about 164,000 fuel units per transaction. Its observer derives the declared
slots separately, with `Solcore.Abi.V1.Keccak256`, and the adapter checks
them with its own Keccak-256. Lean and Python tests check all three against
`cast keccak`. The declared-slot Hull runner serves the profile unchanged.
The profile is a twenty-fourth suite profile with one new native tool; the
seventeen other native tools are byte-identical to main's. Generation reserves
the measured 93-node wrapper before generating the step. Three keys from a
bank with successor pairs and the maximum, three inputs and one of four
completion patterns come from a separate high-bit stream. All 300 of the
first 300 seeds at 384 nodes were accepted. A case embeds the closure, so a
native shrink response carries at most sixteen candidates to fit the
campaign's 4 MiB bound on tool output.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions. Its slots, from `cast keccak`, and its histories were computed
outside Lean by a separate evaluator of the step programs and a direct model
of the protocol. A registered Lean validator confirmed every declared slot
list, status, payload and slot against original Core and rejected tampered
entries, including slots in Solidity's order. Coverage includes all 39 step
features of the corpus, the six storage boundary inputs, the whole key bank
(0, 1, 6, 7, 2^255 and 2^256 - 1), the three static alias kinds (a repeated
key, a successor key and the maximum key, whose successor wraps), one to
three helpers and transactions, four templates, both outcomes and six
completion patterns. The calldata of all 33 fixed and 48 random transactions
matched `cast calldata`.

The full Lean build (10,067 jobs), registered tests, kernel policy and 516
Python policy tests passed. The fixed suite matched all 12 scenarios and 33
prefixes on Sonatina O0 and O2 (75.3 and 75.0 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
sixteen attempts with no exclusions. Both levels matched all sixteen and 48
prefixes (105.1 and 102.7 seconds), covering the whole key bank and all three
alias kinds. Neither random run produced a finding.

A copied Hull difference in the entry slot of key 7 at the last of three
transactions was reduced on each level to that transaction with key 6, whose
successor entry is that slot, zero input and flags and a reduced step: seven
accepted reductions in eleven actual candidate executions. The four rejected
candidates lowered the key to 0 or 1 and no longer declared the slot. A copied
counter difference at a reverted last transaction was reduced on each level
to that transaction, still reverting, with key and input zero: 37 accepted
reductions in 38. Original and reduced archives replayed exactly with
agreement (eight replays), and synthetic fingerprints reproduced. Core or Hull
fuel one was inconclusive. With the extended storage and suite scripts, the
storage, rollback, call, keyed, dynamic-array, log, call-value, bytes and
forwarded-value fixed corpora still matched all 119 scenarios and 329
prefixes on both levels. An offline preparation of the worktree's cloned
cache verified all eighteen native tools as ready. Hosted CI has not been
run.

This scope does not compare gas, balances, nonces, code or memory, other key
or value types, other base slots, nested mappings or Solidity's slot order.
Agreement is test evidence, not a preservation proof.

The eighth extension, `stateful-ledger`, keeps the mapping layout but keys
entries by `msg.sender`, so that several funded senders act on one ledger.
Original Core needs no change. It reads the sender with the `callerAddress`
host request, which `ContractRuntime` answers with each invocation's caller,
and it hashes slots with the mapping profile's Keccak closure. A probe
confirmed that the pinned compiler accepts the contract's `caller()` and `>`
on Words at O0 and O2. On Hull, the same probe stored a sender's entry at
`keccak256(1 ++ sender)` and reverted an insufficient transfer with the
credited balance. The keyed Hull runner requires one caller, so a new runner
accepts per-call senders from a declared set. Its definitions were fixed
before execution:

- Senders: three fixed funded senders, Anvil's first three default accounts,
  with the first as the deployer. Each transaction names its sender. Original
  Core invokes the transaction with that caller over a world that holds an
  empty account for each sender. The Hull runner uses the sender as the call
  context's caller. The EVM path sends from that unlocked account, which Anvil
  funds with its default 10,000 ether for gas. Balances are not observed.
- Transactions: one to three zero-value calls of `run(uint256 flags, uint256
  recipient, uint256 amount, uint256 input)` with exactly four ABI Words, on a
  contract with the mapping profile's `counter` and `entries` fields.
- Effects: credit `B = entries[sender] + step(input)`. If the amount exceeds
  `B`, revert with `B` and write nothing. Otherwise write
  `entries[sender] = B - amount`, then
  `entries[recipient] = entries[recipient] + amount`, so a self-transfer
  leaves `B`. Then increment the counter and return the reread sum of the
  sender's entry, the recipient's entry and the counter. Odd flags revert with
  that sum after the writes.
- Committed observations: status, payload and the committed values of the
  declared slots after every transaction on all three paths. The declared
  slots are slot zero and `keccak256(1 ++ k)` for every transaction's sender
  and recipient `k`. As for the mapping, the Hull and EVM paths must show no
  nonzero committed slot outside the declaration.
- Ledger protocol: odd flags revert. An even-flag revert is an insufficient
  balance, so its payload is below the amount. A revert keeps every declared
  slot. A returned transaction increments the counter, changes no declared
  slot other than the counter and the two entries, and returns their sum. A
  transfer to another key credits the recipient with exactly the amount and
  leaves a sender entry that the amount does not wrap; a self-transfer leaves
  an entry of at least the amount.
- Rollback and deployment: as for the mapping. The first sender deploys.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, an earlier sender for one transaction, a bank recipient, amount or
  input, and flags reduced to their parity or with the revert bit cleared.
  Candidates are ordered by transaction count, distinct senders, program
  complexity, then the sum of sender positions, flags, recipients, amounts and
  inputs. They rederive their declared slots.

Original Core invokes each transaction with its sender as caller, over a world
with an empty account per sender, and its observer derives the declared slots
with `Solcore.Abi.V1.Keccak256`. A new Hull runner,
`rust-hull-ledger-scenario`, accepts the declared senders; the keyed runner is
unchanged. The adapter sends each EVM transaction from its sender after
checking that Anvil unlocks all three. It checks the ledger protocol from each
row and the prior slots without evaluating the step. The profile is a
twenty-fifth suite profile with two new native tools; the eighteen other
native tools are byte-identical to main's. Generation reserves the measured
115-node wrapper. Three senders, recipients, amounts and inputs and one of
four flags patterns come from a separate high-bit stream. All 300 of the first
300 seeds at 384 nodes were accepted. Their 900 transactions returned 612
times, reverted on odd flags 217 times and reverted for an insufficient
balance 71 times.

The fixed corpus has twelve scenarios (eight imported, four generated) and 32
transactions. Its slots, from `cast keccak`, and its histories were computed
outside Lean by a separate evaluator of the step programs and a direct model
of the protocol. A registered Lean validator confirmed every declared slot
list, status, payload and slot against original Core. It rejected tampered
entries, including a sender slot in Solidity's order and another sender.
Coverage includes all 33 step features of the corpus, the six storage boundary
inputs, all three senders, the whole recipient bank (the three senders, 0,
2^160 - 1 and 2^256 - 1) and amount bank (0, 1, 7, 2^64 - 1, 2^64 and 2^70),
and one to three distinct senders. It also includes both revert causes, the
three alias kinds (a self-transfer, a sender that an earlier transaction paid,
and a repeated sender), one to three helpers and transactions, four templates,
both outcomes and seven completion patterns. The calldata of all 32 fixed and
48 random transactions matched `cast calldata`.

The full Lean build (10,084 jobs), registered tests, kernel policy and 526
Python policy tests passed. The fixed suite matched all 12 scenarios and 32
prefixes on Sonatina O0 and O2 (76.2 and 75.6 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
sixteen attempts with no exclusions. Both levels matched all sixteen and 48
prefixes (109.8 and 128.5 seconds), covering every sender, recipient and
amount, one to three distinct senders and both revert causes. Neither random
run produced a finding.

A copied Hull counter difference at an insufficient-balance revert, after
transfers from the two other senders, was reduced on each level to that
transaction from the first sender, with recipient zero, amount one and input
zero: nine accepted reductions in eleven actual candidate executions. A copied
difference in that transaction's sender slot was reduced to the same
transaction from the first sender, paying the third sender, which keeps the
slot declared: eight accepted reductions in seventeen. Earlier senders were
rejected while they dropped the slot. On a generated three-helper step, a
sender-slot difference reached the 64-attempt limit with eleven accepted step
reductions, because every sixteen-candidate batch began with step candidates.
Original and reduced archives replayed exactly with agreement (twelve
replays), and synthetic fingerprints reproduced. Core or Hull fuel one was
inconclusive. With the extended storage and suite scripts, the storage,
rollback, call, keyed, dynamic-array, log, call-value, bytes, forwarded-value
and mapping fixed corpora still matched all 131 scenarios and 362 prefixes on
both levels. An offline preparation of the worktree's cloned cache verified
all twenty native tools as ready. Hosted CI has not been run.

This scope does not compare gas, balances, nonces, code or memory, other
senders, value-bearing transfers, contract callers, other key or value types
or Solidity's slot order. Agreement is test evidence, not a preservation
proof.

The ninth extension was to compare ABI-encoded multi-word return values on all
three paths. Original Core cannot produce them without a change. Its two
contract entry conventions, `returnWord` and `wordOutcomeV1` in
`CoreContractEntryProfile`, decode the result into exactly one Word of return
data, and no host request writes return data. A static tuple or a `bytes`
return would need a new entry convention, with its decoding lemmas, in the
shared contract runtime. That lies outside this work's files and would change
Core's runtime interface, so the fallback was built instead.

The fallback, `stateful-long-bytes`, takes the bytes profile's protocol from
two 32-byte chunks to eight, so payloads reach 256 bytes. The pinned decoder
then copies up to eight Words into memory, and both Core and the source read
every chunk. Its definitions were fixed before execution:

- Transactions: one to three zero-value calls of `run(uint256 flags, bytes
  payload)` with the canonical ABI encoding: the head, the tail offset 64, the
  length and the payload zero-padded to whole Words, with at most 256 payload
  bytes. Other encodings are outside the scope.
- Effects: chunk `k`, for `k` from 0 to 7, is present when the length exceeds
  `32k`. It is the payload's Word at that position, with bytes at or past the
  length read as zero. Starting from slot zero, the accumulator becomes
  `step(accumulator + chunk)` and is written to slot `1 + k`. Then the
  accumulator goes to slot zero, the running byte count plus the length to
  slot nine and the last payload byte, or zero when the payload is empty, to
  slot ten. The result rereads slots zero, nine and ten and adds the calldata
  size. Odd flags revert with it after the writes.
- Committed observations: status, payload and slots zero through ten after
  every transaction on all three paths. The Hull and EVM paths must show no
  nonzero committed slot outside them.
- Protocol: odd flags revert and a revert keeps the eleven slots. A returned
  transaction adds its length to slot nine, leaves its last byte in slot ten
  and returns the committed slots zero, nine and ten plus its calldata size,
  `100` plus the payload length rounded up to a whole Word.
- Rollback and deployment: as for the bytes profile.
- Sequence reduction: as for the bytes profile, truncating to the new length
  bank: checked step reduction, transaction removal with stable IDs, a shorter
  bank length, zeroed payload bytes, and flags reduced to their parity or with
  the revert bit cleared. Candidates are ordered by transaction count, program
  complexity, total payload length, then flags and payload bytes.
- Node budget: the eight chunk guards are a fixed part of the wrapper. Like
  the mapping's Keccak closure, they lie outside the step's node budget.

Original Core folds the eight chunks with the bytes profile's chunk
expression; with two chunks and slots three and four it is exactly the bytes
contract. The adapter, campaign and suite treat the profile as a bytes profile
with its own payload bound, observed slots and count and last-byte slots, so
the bytes profile keeps its 64-byte bound. The profile is a twenty-sixth suite
profile with one new native tool; the twenty other native tools are
byte-identical to main's. The eight chunk guards (296 nodes) lie outside the
step budget, so generation reserves the measured 102-node wrapper. All 300 of
the first 300 seeds at 384 nodes were accepted, and their 900 transactions
used every bank length. A case reaches about 75 KB, so a native shrink
response carries at most 32 candidates.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions. Its histories were computed outside Lean by a separate evaluator
of the step programs and a direct model of the protocol. A registered Lean
validator confirmed every status, payload and slot against original Core and
rejected tampered entries. Coverage includes all 31 step features of the
corpus, the six boundary Words as chunks, one to three helpers and
transactions, four templates, both outcomes, six completion patterns, all
twelve bank lengths and reverted payloads of 0, 65, 97, 128, 223, 255 and 256
bytes. The calldata of all 33 fixed and 48 random transactions matched `cast
calldata`.

The full Lean build (10,099 jobs), registered tests, kernel policy and 532
Python policy tests passed. The fixed suite matched all 12 scenarios and 33
prefixes on Sonatina O0 and O2 (76.7 and 76.5 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
sixteen attempts with no exclusions. Both levels matched all sixteen and 48
prefixes (107.5 and 105.6 seconds), covering every bank length. Neither random
run produced a finding.

A copied Hull difference in slot 8, which only payloads of more than 224 bytes
write, at the first of three transactions was reduced on each level to that
transaction with an empty payload and a reduced step: five accepted reductions
in seven actual candidate executions. Original and reduced archives replayed
exactly with agreement (four replays), and synthetic fingerprints reproduced.
Core or Hull fuel one was inconclusive. With the extended storage and suite
scripts, the storage, rollback, call, keyed, dynamic-array, log, call-value,
bytes, forwarded-value, mapping and ledger fixed corpora still matched all 143
scenarios and 394 prefixes on both levels. An offline preparation of the
worktree's cloned cache verified all twenty-one native tools as ready. Hosted
CI has not been run.

This scope does not compare multi-word return values, payloads longer than 256
bytes, strings, gas, balances, nonces, code or memory, non-canonical encodings
or the decoder's revert paths. Agreement is test evidence, not a preservation
proof.

Further state/ABI work, such as nested or multi-word ABI elements, `bytes`
beyond 256 bytes, strings, ABI-encoded return values, which first need a
contract entry convention for more than one Word, or callers beyond the three
fixed senders, needs its own observation, rollback, deployment and reduction
definitions first.
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

The first expression closure (`CellAwareInvocationAcceptedExpressions`)
discharges accepted-expression meaning for named-row bodies whose accepted
expressions are all literals, ordinary local reads, groups, pairs, primitive
unary and binary operators or conditionals (`Closed`). It extracts each receipt
tree from the actual named compiler's acceptance and closes it by structural
recursion, and its `body_preserves` and `body_reflects` are whole-body theorems
without the `Expressions` premise. In its place they take `Closed`, the
read-fault interpretation (`Reads`) and selected-body typing of the staged
registry. Other
expression forms and every expression of a contextual closure still need the
premise. A direct call is preserved and reflected at an accepted site when the
callee's application meaning holds below the grade of the call
(`CellAwareInvocationAcceptedDirectCalls`). The head's caller carrier retains
every ordinary global slot; the cell producer of
`CellAwareInvocationAcceptedGlobalSlots` lets accepted bodies run on such a
protocol. `CellAwareInvocationAcceptedNamedApplication` derives the head's
input from the callee's own accepted body on that protocol, given the meaning
of the body's accepted expressions below the grade; for a callee whose accepted
expressions lie in the closed subset, the input holds at every grade. Direct
calls at expression roots, with first-subset arguments, extend the subset
(`CellAwareInvocationAcceptedCallTrees`,
`CellAwareInvocationAcceptedCallExpressions`). One strong induction on the
grade closes every family of rows whose bodies call only admitted
instantiations (`CellAwareInvocationAcceptedCallFamily`). A complete inventory
supplies the call authority (`CellAwareInvocationAcceptedCallAuthority`). In the
preservation direction, the unchanged public root runs a call-containing row on
the slot-retaining protocol (`CellAwarePublicAcceptedCallRoot`). Root
reflection, the lifting of original traces of call-containing bodies, a
one-call instance and nested calls remain. Contextual-view writes and matches
are not yet closed.

For these named rows the subset is connected to the unchanged public root
(`CellAwarePublicAcceptedNamedRoot` and `CellAwarePublicAcceptedNamedForward`).
The actual named parameter entry constructs the body's physical entry state,
and the public diagnostic receipt supplies `Reads` and the write inputs
(`CellAwareInvocationAcceptedNamedInvocation`). The write inputs interpret
operand and unary diagnostic words at the typed assignment occurrences of the
Source; the earlier statement over every site had no instance under the actual
fault relation. A staged Source trace is related to native completion of the
actual public start in both directions. A returning trace reaches a successful
`SourceCoreExecution` resumption with the exported value and the returned
session's physical history. `Closed`, the body receipt and its coverage and the
original compilation receipt remain premises. Generalized declarations are not
connected, and later calls do not yet chain from the reached history, which
uses the accepted instance model. The design document lists the remaining
premises.

Statement lists beyond a single return are closed as well
(`CellAwareInvocationAcceptedBodyShape` and
`CellAwareInvocationAcceptedStatementLifting`). For returns, monomorphic
declarations, refined bare assignments, expression statements, blocks and
conditionals whose expressions are subset sites, every refined accepted tree is
covered, and every ordinary execution, in both compiler modes and with every
control outcome, is a staged execution. One actual row meets every premise
(`SourceCoreGeneralizedExportAcceptedTick`). At `tick` of the GeneralizedExport
program, runtime checks of its expression nodes and statement shape supply
`Closed` and the coverage of its refined accepted tree, the public compilation
supplies the original compilation receipt, and the row's independent Source
execution is lifted to the staged trace. The output and both checkpoint
theorems are applied together at the first public call. Fault executions are
not lifted, and no instance yet exercises declarations, assignments,
conditionals or operators.

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
connected unit without an algebra library.

Creation attempts refused before init code runs are connected. Independent
rules cover a static frame, init code over EIP-3860's 49,152 bytes, a missing
gas observation, an unaddressable init range, the depth limit, an insufficient
endowment and EIP-2681's nonce limit. Refusals keep the creator nonce,
balances, accounts and logs; the last three expand memory over the init range
and clear return data. The proof reaches the actual CREATE lowering,
`Creation.invoke`, the funds and nonce checks of `CreationRuntime.dispatch` and
the create handler installed by `objectHandlers`, all restated by `rfl`. The
call-mode and root-reentry public theorems cover the refusals without
statement changes. Eight independent source scenarios reach the call-mode
theorem, with runtime checks of receipts, balances and nonces; the depth
refusal has no public consumer because it needs a frame at depth 1024.

Admitted CREATE and CREATE2 attempts that run no init frame are connected.
Independent rules derive the CREATE address from the RLP of the creator and
its nonce, and the CREATE2 address from 0xff, the creator, the salt and the
init-code hash, using the connected Keccak; the kernel reproduces the 11
recorded reference vectors. A nonzero nonce or code size at the address is a
collision that returns zero and keeps the advanced nonce. An address absent
from a complete world receives a new account and the endowment, and empty
init code deploys empty code without an init frame. The proof reaches the
actual address builders, nonce write, checkpoint, collision checks, transfer
and installation, restated by `rfl`, and four independent source scenarios
reach the call-mode theorem with runtime checks. The two faults after the
nonce advance are connected as well: an unknown target, absent from an
incomplete world or recorded with unknown code, is failure 7, and an
endowment that would overflow the target balance is failure 12. Both restore
the post-nonce checkpoint through the actual restoration code, and four more
source scenarios reach the call-mode theorem. Init frames remain: nonempty
init code in a deployment context, runtime-code validation and installation,
and rollback with revert bytes. Their source rule needs an init-template
catalog and a premise connecting it to the compiled init definitions, which
changes the public theorem statements; the Hull design document lists the
remaining source rules and proof obligations.

Hull's explicit revert is connected. Its independent rule stores the message,
at most one word of UTF-8 bytes, left-aligned at memory offset zero and
reverts with exactly the message bytes. The call-mode effects use the rule, the
common recursive proof gains a separate revert obligation that only the
call-mode layer discharges, and four independent source scenarios reach the
call-mode theorem with runtime checks of the revert bytes. No public theorem
statement changes.

Inline Yul is connected for statement lists: `let` with one name and an
optional value, assignment to one name, expression statements, nested blocks,
`if` and `switch`, over literals, Yul and Hull word locals and nested calls of
`mload`, `msize`, `mstore`, `mstore8`, `return` and `revert` and of the word
operations `add`, `sub`, `lt`, `gt`, `eq` and `iszero`. Arguments are
evaluated from right to left, which nested calls with effects observe; the
locals of a nested body end with it, and a `return` or fault in a nested body
stops the block. A separate assembly obligation, which only the call-mode layer
discharges, connects the actual `YulLowering` builders by induction over the
source derivation; the builders are public for the proof, a visibility-only
change. The effect builtins go through the frame model's `BuiltinStep`; the
word operations compile to pure Core primitives, which one proof covers for
every model. Five independent source scenarios reach the call-mode theorem
with runtime checks: one whose returned word depends on the argument order, one
that assigns and reads a Hull local, one with `if` and a nested block, one
with two `switch` statements, and one that uses all six word operations,
including a subtraction that wraps, besides the four one-call scenarios. `for`
with `break` and `continue`, local functions, multi-name `let` and assignment,
string literals and other builtins remain in assembly, followed by object
linking; the Hull design document lists what `for` needs.

## Handoff rules

Use separate commits for a coherent operational change and its validation.
Keep `questions.md` ignored and uncommitted; put confirmed regressions and
public limitations in tracked tests and documentation. Update this roadmap
when a gate is actually complete, with the commands and observed results.
Delete disposable exports and validation caches once their evidence is saved.
