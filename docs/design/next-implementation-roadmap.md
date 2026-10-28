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
| 1 | CI and continuous bounded random campaigns across all existing profiles | Local gate complete; continuous fuzzing driver implemented; automatic CI triggers disabled, manual dispatch only; no passing hosted run yet | Reproducible CI jobs, scheduled seed exploration, retained findings and verified cancellation/resource limits. |
| 2 | Generated Sonatina O2, then Yul comparisons | Local gate complete; the sixteen storage-family profiles also run on Yul when selected and are validated locally; the two call profiles stay on Sonatina | The same original cases run on each enabled backend with explicit backend provenance and replay. |
| 3 | Missing runtime operation mappings | Implemented; O2 random run has a recorded finding | Tested Rust-dialect mappings, dynamic-input regressions, generation, reduction and replay for each added operation. |
| 4 | Richer generated grammar | Call-graph, loop and aggregate families validated locally; G0 generator revision four, revision three's per-case swarm masks restricted to each emitter's features, is the random default for the sixteen G0-based pure profiles; random runtime-input campaigns add four seeded inputs to each function's boundary inputs, can request whole functions and, in the eleven profiles whose functions can be identities, exclude functions that return every boundary input unchanged, generating whole functions in as many case-tool requests as the 2 MiB response limit needs; nested bounded loop, bounded recursion, inline Yul, loop-closure, recursive-loop and inline Yul loop profiles are validated locally on O0, O2 and Yul; pure campaigns compile each distinct source once per backend; an O2 random comptime run, the O0 and Yul random inline Yul runs and the O0, O2 and Yul random inline Yul loop runs have recorded compiler crashes; hosted run pending | Broader typed compositions with bounded generation and reductions that preserve binding, effects and failure identity. |
| 5 | A minimal proof for the actual Rust-dialect emitter | Closed, runtime-input, named-helper, raw-primitive, call-graph, private-mutation, aggregate, aggregate call-graph, call-graph loop, aggregate loop, generic, two-slot storage, two-slot rollback, keyed-storage and event-log emitters proved locally; other emitters open | A small connected meaning-preservation theorem for what is actually emitted, not for a substitute native Lean syntax. |
| 6 | State and ABI extensions | Keyed-storage, bounded dynamic-array, event-log, call-value, bounded-`bytes`, contract-forwarded value, Keccak-addressed mapping, sender-keyed ledger, 256-byte `bytes`, nested `uint256[][]`, malformed-calldata, several-methods and storage-loop extensions validated locally, malformed calldata for the dynamic-array, nested-array and 256-byte `bytes` contracts and comparing std error reverts by selector, two to four external methods on one contract dispatched as std does, and a bounded source loop whose iterations read and write declared slots; all eighteen stateful profiles compare the observed contracts' whole committed storage on all three paths; random stateful campaigns generate steps with G0 revision three and sequences of up to eight transactions; multi-word return values need a contract runtime change; O2 random log, forwarded-value and dynamic-array runs have recorded compiler crashes; hosted run pending | Explicit additional observations and transaction semantics, with actual three-way tests and sequence reduction. |
| 7 | Native Source goal two | In progress: statement closure over the actual compiler tree, a first expression subset and statement shape for named rows, their public-root connection, one concrete instance, direct calls at expression roots closed by one size induction over a family of rows, call authority from a complete inventory, and the public root's preservation direction for call-containing rows; root reflection, lifting of call-containing bodies, a one-call instance, nested calls, remaining expression and statement forms, fault lifting, a richer instance and chained public calls remain | Complete accepted-body preservation and connect all actual passes to the public session. |
| 8 | Remaining Hull public connections | In progress: identity, SHA-256 and RIPEMD-160 precompiles, refused CREATE/CREATE2 attempts, admitted attempts without an init frame and the init-template catalog premise of the public theorems, Hull's explicit revert and inline Yul statement lists with locals, assignments, nested blocks, `if`, `switch`, nested memory and termination calls and the word operations `add`, `sub`, `lt`, `gt`, `eq` and `iszero` connected | Independent semantics through actual lowering, initialization and public execution for each remaining feature. |

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
  The automatic triggers were later disabled because hosted runs took too
  long; the workflow now runs only on manual dispatch.
- `semantic-fuzz.py` adds continuous operation on one machine: advancing root
  seeds per iteration, an epoch over the prepared tools and harness scripts,
  a registry that counts every finding occurrence by signature and keeps the
  first examples, pruned run records, triage labels and reports. See
  [continuous fuzzing](../../scripts/SEMANTIC_CI.md#continuous-fuzzing).

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
output and no unresolved libraries or immutable references. The sixteen
storage-family profiles are admitted under the stateful Yul boundary below,
which names the first fifteen; `stateful-storage-loops` joined later under the
same boundary. The two call profiles, other code-observing programs and
arbitrary nested objects remain excluded until their layout and observation
boundary are connected explicitly. This scope does not require bytecode-layout
or gas equality between the three paths.

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

### Stateful Yul boundary

These definitions were fixed before execution. The fifteen storage-family
profiles also run on Yul:
- `stateful-storage` and `stateful-storage-rollback`;
- `stateful-keyed-storage`, `stateful-dynamic-array` and `stateful-logs`;
- `stateful-call-value`, `stateful-bytes` and `stateful-long-bytes`;
- `stateful-mapping`, `stateful-ledger` and `stateful-nested-array`;
- `stateful-malformed-calldata`, `stateful-malformed-nested-array` and
  `stateful-malformed-bytes`;
- `stateful-methods`.

The call profiles `stateful-calls` and `stateful-forwarded-value` stay on
Sonatina. Each of their sources compiles two contracts, a parent and the child
it calls, so it needs two creation/runtime pairs; the Yul export admits one.

A feasibility probe preceded these definitions. For the first four scenarios
of each fixed corpus, it compiled the checked Rust driver's Yul with the
pinned solc. That is 60 scenarios over twelve wrappers; the three malformed
profiles reuse the dynamic-array, nested-array and 256-byte `bytes` wrappers.
The probe then ran the unchanged storage adapter with the EVM deploying those
bytes:
- Every compilation was one creation object with one runtime sub-object. It
  had no data sections, other objects, or link or immutable references, and at
  most 1,489 creation and 1,443 runtime bytes. The checked Hull had one
  deployment object with one leaf runtime object.
- The runtime code reads no code. `codecopy`, `codesize`, `dataoffset` and
  `datasize` occur only in the creation code, which copies its own runtime
  object. Neither part uses `create`, a call, `extcode*`, `selfdestruct`, a
  balance read, `gas` or transient storage.
- Every deployment's prestate diff reported no storage, so the EVM contract
  starts empty as on the other paths.
- All 60 scenarios and their 173 transactions matched on all three paths. They
  include 23 rows compared by std's error selector, 9 logs and two nonzero
  deployment values.

Nothing shared changed: not the runtime, the Hull importer, the declared-slot
runners or a proof.

**Paths:**
- Original generated Core.
- The Yul EVM. It deploys the creation bytes of one solc compilation, checks the
  installed runtime against that compilation's deployed bytes, and mines every
  transaction.
- Imported Hull linked with separately validated Sonatina O0 images. As for pure
  Yul, it is an additional reference, not Yul-linked Hull execution.

Reports record `backend` `yul` and the `pathBackends` of pure Yul:
`original-core`, `sonatina-o0` and `yul`.

**Observation boundary.** The Yul EVM path supplies the same observations as
Sonatina, from actual mined transactions and receipt-block state:
- each transaction's completion and its returned or reverted bytes, with std's
  error selectors under the unchanged selector rule;
- the declared committed slots and, where declared, the absence of nonzero
  undeclared slots;
- the contract's whole committed storage after deployment and after every
  transaction, from prestate diffs and receipt-block rereads;
- ordered committed logs, from receipts and the chain's log list;
- for `stateful-call-value`, the call value and the contract's committed
  balance;
- for `stateful-ledger`, the fixed senders.

None of these depends on code layout: the runtime reads no code, and the
creation code reads only its own runtime object. Gas, bytecode layout, code
size and optimizer internals are not compared.

**Admission.** `export-rust-yul.py` admits the sixteen pure wrappers and the
twelve storage-family wrappers, each list taken from its adapter's profile
table. The shape checks above are unchanged. Wrapper names and shape do not
establish scope: the storage adapter validates and natively replays the case
before the export, as the pure adapter does.

**Selection.** The storage adapter and campaign accept `--backend yul --solc
PATH`. Exact replay inherits the backend and checks the Yul evidence as for pure
Yul. The suite runs the storage-family profiles on Yul when they are selected;
its default Yul selection stays the sixteen pure profiles. A call profile with
`--backend yul` is refused before execution.

**Validation before results:**
- fixed Yul matrices of the fifteen storage-family corpora;
- random Yul runs of each profile with sixteen scenarios of eight transactions,
  G0 revision three with swarm masks, at the suite's default node budgets.

**Results.** The gate passed on the final tree before the code commit
`c159b604e`: the full Lean build and tests, the kernel check, 718 Python tests,
every corpus check and the diff check. The matrices ran on that commit with 89
digests frozen: scripts, native tools, solc, Anvil, and the Rust driver and
code-image exporter. None changed during any run.
- **Fixed Yul suite:** all fifteen storage-family corpora matched, 190
  scenarios and 524 prefixes with complete coverage, in 1,804 seconds. 61 rows
  compared by std's error selector, 27 logs and five nonzero deployment values
  matched. Every report recorded the Yul export and `pathBackends`, and every
  deployment's prestate diff was empty.
- **Random Yul suites:** root seed `20261028`, sixteen eight-transaction
  scenarios per profile with G0 revision three. All 240 scenarios and 1,920
  prefixes matched, in 2,433 seconds. Generation took 248 attempts, with eight
  ordinary budget exclusions and no resource exclusion. 257 rows compared by
  selector, 83 logs and eight nonzero deployment values matched.
- **Sonatina O0 on the same code:** the storage, call-value and several-methods
  corpora still matched, 36 scenarios and 99 prefixes.

Neither suite produced a finding. A Yul scenario took about 1.6 times as long
as on O0, because each compiles its own Yul through a second checked Hull
export and solc. That is about 9.5 seconds per fixed scenario and 10 per random
one. Hosted CI has not run these profiles.

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

**G0 generator revision two.** Random mode now generates the eleven G0-based
pure profiles with `core-g0-v2/lcg64-v1`; the three call-graph families keep
their own grammars. Revision one took every choice from the low bits of the raw
LCG state, whose bit 0 alternates, so the kind of a literal followed its
position in the stream. Over 1,024 consecutive seeds at a 32-node budget,
0.2% of adjacent literal pairs and none of the 380 binary operations with two
literal operands were both edge values, only 22.8% of literals came from its
eight-value bank, and the root forms of consecutive seeds always advanced by
three or five. A Word binary operation's leaf left operand was always a random
Word outside a `let` and always a variable inside one, so `byte` and
`signextend` never received a literal index below 256 in 2,000 programs at the
primitive profile's budget.

Revision two keeps the forms and budget split. Each draw passes through the
SplitMix64 finalizer and each choice takes its upper 32 bits. A literal
decides edge versus random from its own draw, half each, and the edge value is
uniform over a 32-entry bank of shift counts, byte and sign-extension indices,
width masks and their successors, limb boundaries, the address mask and the
int256 limits. The same sample then has 25.6%, 50.5% and 23.9% adjacent pairs
that are both edge, mixed and both random, 50.6% bank literals, every bank
value at least 73 times and all six root-form steps. High bits alone, without
the finalizer, still locked consecutive seeds to four of the six steps.

Revision one stays bit for bit. The case tool keeps it when no version is
given, the campaign passes each manifest's own version, and all eleven G0
manifests record it. The new case tool and a build at the base commit gave
identical output for 88 generation runs over all fourteen generate commands,
with and without an explicit `v1`, and for the replay, reduction and
observation of 81 cases. Cases, reductions and campaign summaries record the
revision; replay regenerates seeded cases with the recorded one. The stateful
profiles still build their aggregate steps with revision one under their own
tools.

The full Lean build (10,134 jobs) and registered test driver passed, including
new tests for the revision-two vectors, bounds and statistics and for
revision-two generation, replay, tampering and reduction in all eleven
profiles. The Python policy suite passed 559 tests, and the ten fixed-corpus
validators passed unchanged. With root seed 1 and sixteen cases each,
`closed-g0`, `runtime-primitives` and `runtime-aggregates` matched all
forty-eight revision-two cases on O0 and on O2, in 223 and 219 seconds, with 65
ordinary generation exclusions, no resource exclusions and no findings. A
revision-one and a revision-two case of the closed and primitive profiles each
replayed exactly from its archive, and 64 cases saved by earlier campaigns
replayed unchanged. Hosted CI still has not been run.

**Seeded runtime inputs.** Random campaigns of the thirteen runtime-input pure
profiles, including the three call-graph families, now run each accepted
function at its boundary inputs and then at four inputs derived from the case
seed: a full random Word, a Word of uniform bit width, a value below 512 and
the negation of another uniform-width value. They come from a domain-separated
SplitMix64 stream of the case seed. A generated origin names the selection
`seeded-inputs-v1/splitmix64`; replay recomputes the list, and an origin
without it means the boundary inputs alone, as in every fixed corpus. The
generation commands take the selection as an option, the campaign passes it in
random mode, corpora refuse it and saved cases keep theirs. The admission
filters still use only the boundary inputs, and `--cases` still counts inputs,
so a sixteen-case run of a four-input profile now covers two functions.

The new case tool and the previous build gave identical output for 244
generation runs over all fourteen generate commands, with no option and with
explicit G0 versions, and for the replay, reduction and observation of 227
cases. The full Lean build (10,137 jobs) and registered test driver passed,
including value-range checks over 2,048 seeds and seeded generation, replay,
tampering and reduction in all thirteen profiles. The Python policy suite
passed 592 tests and the ten fixed-corpus validators passed unchanged. With
root seed 1 and sixteen cases each, `runtime-word`, `runtime-primitives`,
`runtime-loops` and `runtime-call-graphs` matched all 64 cases on O0 and on
O2, in 304 and 306 seconds, twenty of them at seeded inputs, with no findings.
Seeded small and negated inputs of `runtime-word` and `runtime-call-graphs`
replayed exactly from their archives.

**G0 generator revision three.** Random mode now generates the eleven G0-based
pure profiles with `core-g0-v3/lcg64-v1`: revision two's grammar under a swarm
mask drawn once per case from its seed and shared by all of the case's G0
programs. Each of the 26 operators and non-leaf forms is enabled by its own
bit of one mixed draw, 13.0 on average. A form drawn as in revision two but
disabled is replaced by a uniform second choice among the enabled non-leaf
forms. Leaves therefore keep their probability and programs their size; a first
version that let disabled forms fall to leaves lost a quarter of the operators.
With the full mask nothing is redrawn and revision three is revision two.
Cases record the mask in `provenance.swarmMask`; replay requires it for
revision three, checks it against the seed and refuses it on other revisions,
and reductions copy it.

Over 1,024 seeds at 32 nodes, masked programs kept revision two's size (7,153
operators against 7,281) and slightly more depth, used 18% fewer distinct
operators, put an operator directly inside itself nearly twice as often (934
against 486 times) and gave 19% more distinct operator pairs across the sample
(508 against 428); at 64 nodes the same comparisons held. Random campaigns
have no coverage requirements of their own, since manifests supply them all,
so no requirement changed and fixed corpora stay on revision one.

The new case tool and the previous build gave identical output for 388
generation runs, every existing form including explicit revision two and
seeded inputs, and for the replay, reduction and observation of 360 cases.
The full Lean build (10,140 jobs) and registered test driver passed, with new
tests for the mask catalog, vectors and frequencies, equality with revision two
under the full mask, mask conformance and the shape statistics, and for masked
generation, replay, tampering and reduction in all eleven profiles. The Python
policy suite passed 592 tests and the ten fixed-corpus validators passed
unchanged. With root seed 1 and sixteen cases each, `closed-g0`,
`runtime-primitives`, `runtime-aggregates` and `runtime-comptime` matched all
64 cases on O0 in 313 seconds. On O2 the first three matched, but all eight
inputs of one `runtime-comptime` function crashed the compiler during code-image
export with `arithmetic operation overflow` in `primitive-types`, the panic
recorded earlier for the event-log profile; checked Hull export succeeded.
Automatic reduction kept the fingerprint. That O2 random gate failed. Per the
user's instruction, the symptom is recorded without upstream investigation.

**Shared compilation.** Checked Hull and code-image export took 3.9 of 4.5
seconds per random `runtime-word` case on O0, yet depend only on the source. A
pure campaign now compiles each distinct source once per backend and reuses
the result for every case whose source files, backend, library, exporters and
compiler builds are identical by digest, never by position. The compilation
runs in a directory named by that digest; each case copies all outputs into
its own archive, checks their digests and records the shared compilation and
processes in `report.compilation`. A shared rejection or crash keeps its
category, stage, detail and fingerprint on every case it affects and counts as
an error each time; resource and adapter failures are not shared. Every case
still executes all three paths at its own input. Yul shares its Yul export
with the two Sonatina exports; reductions and exact replay compile on their
own. With root seed 1 and sixteen cases each of `runtime-word`,
`runtime-primitives`, `runtime-loops` and `runtime-call-graphs`, the 64 random
cases took 71 seconds on O0 and O2 instead of 303 and 306, with seven
compilations; the profiles' fixed corpora, 213 cases with 74 distinct sources,
took 455 seconds on each backend instead of 1,032 and 1,020. A reusing case
takes 0.6 to 0.8 seconds. All fourteen pure fixed corpora, 595 cases, kept
their cases, categories, fingerprints and coverage on O0 and O2, as did 176
cases of four corpora on Yul; 44 archives, 39 of them from reused
compilations, replayed exactly on O0, O2 and Yul; and the recorded O2
comptime crash recurred on all eight inputs of its function after one
compilation, with unchanged fingerprints. The Python policy suite (617 tests),
the Lean build and test driver, the tool receipt and the ten fixed-corpus
validators passed.

The measurement also showed that random sources repeat in the scalar G0
profiles: the first 64 functions accepted from seed 1 gave 12 distinct
`runtime-word` sources, 24 for `runtime-functions` and 39 for
`runtime-primitives`, and 51 of the 64 `runtime-word` functions were the
identity. The emitter of the first two rejects the extended operators, which
caused nearly all of their exclusions, while a one-leaf program always passes
as the identity.

Random stateful steps do not repeat that way. Each of the fourteen stateful
profiles generated 64 scenarios under revision three, from its suite seed for
root seed 1 at its default budget, and every one had a distinct step source.
Each step was run in original Core on a bank of sixteen Words:
- no step was constant: every template folds the input into a private cell
  with `+` or `xor`, and generation rejects steps whose boundary inputs agree;
- 89 of the 896 steps, four to nine per profile, were the identity, mostly a
  single helper whose closed scalar is zero;
- 142 more were a pure offset `x + c`;
- distinct behaviours on the bank were 54 to 60 per profile.

The aggregate emitter supports every G0 operator, so 936 attempts had no
operator exclusion. The only exclusions were 40 template-budget refusals, 0 to
12 per profile, the most in malformed calldata, whose wrapper leaves its step
175 nodes.

**G0 generator revision four.** Random mode now generates the eleven G0-based
pure profiles with `core-g0-v4/lcg64-v1`: revision three with each case's swarm
mask restricted to the features the profile's emitter renders. Every emitter
declares them from its renderer's operator predicates, and a registered test
probes all 26 catalog features through each pure emitter and requires a
feature to emit exactly when it is declared. The scalar renderer, used by
`closed-g0`, `runtime-word`, `runtime-functions`, `runtime-mutation` and the
comptime and module constants, renders twelve features; the primitive,
call-graph and aggregate renderers render all 26, so the primitive, aggregate,
loop, generic and closure profiles generate exactly as under revision three. A
comptime or module case records its step's unrestricted mask, and its constant
uses that mask restricted to the scalar renderer. A restriction that would
remove every operator the mask enabled uses the emitter's whole feature set
instead, about one seed in a thousand under the scalar renderer. A case records
its effective mask, replay rejects a mask outside the profile's features, and
reductions copy it. The stateful tools parse versions only up to revision three
and stay on it; fixed corpora stay on revision one.

Over the first 256 functions accepted from seed 1, revision four removed every
exclusion for an unsupported operator, and in the six restricted profiles
attempts per accepted function fell from 4.1–9.8 to 1.0–1.9. Distinct `runtime-word` sources rose from 39 to 188 and
identities fell from 210 to 82; `runtime-functions` rose from 133 to 220
sources with 110 against 36 identities, and one-literal `closed-g0` programs
fell from 174 to 41. The identity remains frequent in `runtime-primitives`
(103 of 256 under both revisions), whose emitter renders every feature, and in
`runtime-word` (82); sources are not deduplicated. Random runtime-input
campaigns also accept `--functions N`, which asks for N accepted functions
with all of their inputs instead of a case count; summaries record
`generation.requestedFunctions` and every count stays per case.

The registered tests probe every catalog feature through every pure emitter
and check revision-four generation, replay, tampering and reduction in all
eleven profiles. The case tool reproduced revisions one to three byte for byte
in 492 generation runs and 4,320 replays, observations and reductions against
the previous build, and the stateful tools reject revision four. Frozen
sixteen-case random matrices of the eleven profiles from root seed 1 matched
all 176 revision-four cases on O0 and on O2. Revision three's O2 matrix again
crashed on the recorded comptime plan; revision four's sixteen cases end before
that plan, which still crashes when generated under revision four. With
sixteen whole functions per profile, revision four found 14 distinct
`runtime-word` sources against 3.

**Boundary identities.** Random campaigns of the ten runtime-input profiles
whose generated functions can be identities now apply the acceptance filter
`exclude-boundary-identity-v1`: after the profile's own filters, it excludes a
function that returns each of its boundary inputs unchanged, under its own
reason and the code `boundary-identity`. The ten are `runtime-word`,
`runtime-primitives`, `runtime-functions`, `runtime-mutation`,
`runtime-aggregates`, `runtime-closures`, `runtime-comptime`,
`runtime-modules`, `runtime-call-graphs` and `runtime-aggregate-call-graphs`.
The two loop profiles already require a changed positive-trip boundary input,
and a generic function returns for input 0 the result of input 1 or its
successor, so neither can be an identity; those three profiles are unchanged.
The filter is versioned in the generated origin's `acceptance` field rather
than as a G0 revision: acceptance belongs to each profile's case module, two of
the ten profiles do not use G0, and only generated cases pass filters, while a
G0 revision is copied into every reduction. Replay applies the recorded filter
again and refuses a saved identity that claims it; an origin without the field,
as in every fixed corpus, applied the profile's own filters. The stateful
profiles and every request without the filter are unchanged.

Over the first 256 functions accepted from seed 1 under revision four, the
filter removed every function that returned all of its recorded inputs:
82 in `runtime-word`, 103 in `runtime-primitives`, 72 in
`runtime-aggregate-call-graphs`, 46 in `runtime-call-graphs`, 36 in
`runtime-functions`, 24 in `runtime-aggregates`, 4 in `runtime-comptime` and 3
in `runtime-mutation`. Distinct `runtime-word` sources rose from 188 to 240 and
`runtime-primitives` sources from 150 to 226, at 2.15 and 3.98 attempts per
accepted function instead of 1.54 and 2.29. No other trivial class forms a
majority; the largest is `runtime-mutation`, which adds a constant to its
input in 112 of 256 functions. The registered tests check that the filter
keeps exactly the functions that change a boundary input, records itself,
replays, refuses a saved identity, composes with seeded inputs and leaves
reductions unfiltered; 666 generation runs and 3,996 replays, observations and
reductions without the filter matched the previous build byte for byte.

Frozen random matrices from root seed 1 ran the eleven G0 profiles and both
call-graph profiles before and with the filter side by side, with eight whole
functions per runtime profile. On O0 both matched all 752 cases of the
profiles that completed, with 92 against 95 distinct sources in 981 against
996 seconds (5.6 against 5.7 sources per minute); on O2 both matched 744 of
752 and crashed on all eight inputs of the recorded comptime plan, with 84
against 87 sources (5.8 against 5.9 per minute) in the completed profiles.
`runtime-word` rose from 7 to 8 sources and `runtime-primitives` from 5 to 7.
Eight loop or closure functions overflowed the 2 MiB limit on one generation
response on both sides; with four functions both profiles matched on both
levels. That limit, not the case count, caps `--functions` for every profile
with large cases: about 6 loop functions at 384 nodes and 64 `runtime-word`
functions.

**Whole-function campaigns past the response limit.** Random generation now
takes as many case-tool requests as a campaign's cases need:

- The first request asks for every case.
- A response over the 2 MiB limit is requested again from the same seed for
  half as many whole functions, and later requests keep that size.
- Each request continues at the seed after the previous request's last
  attempt, modulo 2^64 as the case tool's `Seed.ofNat` reduces it, with the
  attempts left.

Every request but the last asks for whole functions, so the merged cases,
exclusions, attempts and status equal one request's for any request sizes. A
function that alone exceeds the limit stays an inconclusive `output-limit`.
Halving needs no per-profile size table, which seed-dependent case sizes
would make either wasteful or wrong, and it never changes a case.

Evidence and budgets:
- A native check compares one request byte for byte with one-function,
  two-function and halving requests for every pure profile, from seed 1, from
  two below 2^64 and with an exhausted budget.
- Model-based tests cover every request size, retries, a single overflowing
  function, the wrap, exhaustion and malformed responses.
- With `--functions`, the default attempt budget is at least 16 per function,
  up to 10,000, in the campaign and the suite. From six start seeds at each
  bound, the slowest profile needed 6.8.
- The 1,024-case limit and the `--functions` bounds are unchanged.

A frozen O0 random matrix from root seed 1 at `--functions 102`, the loop
bound, matched all 1,020 `runtime-loops` cases and all 816 `runtime-closures`
cases with no output-limit stop. They took 31 and 17 requests with 5 and 4
retries, and compiled 102 distinct sources each, at 2.8 and 3.6 sources per
minute.

**Nested bounded loops.** The first new program shape is
`runtime-nested-loops`: a bounded source `while` loop whose body runs a second
bounded `while` loop around the step. The existing profiles, their corpora,
emitters and emitter proofs stay unchanged; this emitter has no proof yet. The
definitions were fixed before execution:

- Step: an aggregate step DAG of one to three helpers, generated with the
  current G0 revision exactly as for `runtime-loops`, so every G0 feature
  renders and revision four equals revision three.
- Source loop forms. With input `x`, outer mask `O` and inner mask `I`, the
  wrapper sets `acc = x` and runs `x & O` outer iterations. Each outer
  iteration `i` (counting from zero) first sets the inner bound and resets
  the inner counter, then runs `acc = sc_step(acc)` once per inner iteration.
  The inner bound reads one of three things, fixed per plan:
  - `input`: `x & I`, the same in every outer iteration;
  - `counter`: `(i + 1) & I`, which varies with the outer counter;
  - `accumulator`: `acc & I`, read from the value the previous outer
    iterations computed.

  Both counters, the inner bound and the accumulator are declared before the
  outer loop and assigned inside it. The function returns `acc`.
- Bounds: plans admit masks 0, 1 and 3 for both loops; generation draws both
  from 1 and 3. A call therefore runs at most three outer iterations, at most
  three inner iterations in each and at most nine step calls in total. The
  original Core reference is finite: it unrolls three or fewer outer ordinal
  guards, each containing its inner bound and three or fewer inner ordinal
  guards, over one Word cell, and has no counter cell. It is checked by the
  full Core checker and the 512-node case limit.
- Shapes: the twelve combinations of outer mask, inner mask and inner-bound
  form, drawn from a SplitMix64 hash of the case seed so that consecutive
  seeds vary in shape independently of the step's helper count and template.
- Boundary inputs: 0, 1, 2, 3, `2^256 - 1` and `2^255`, which give zero to
  three outer iterations; random campaigns add the four seeded inputs.
- Exclusions, in order: a node budget too small for the shape or above 512, the
  step's own generation exclusions, a step whose four boundary inputs return
  the same Word, fuel exhaustion on a boundary input (an inconclusive resource
  exclusion), and a function that returns every boundary input unchanged
  (`every boundary input returned itself`, code `boundary-identity`). A
  boundary input without a step call returns itself, so the last rule asks
  some input that calls the step to change; the profile needs no acceptance
  filter.
- Specified iterations: each case records the inner trip count of every
  outer iteration it runs. For the `accumulator` form they follow from the
  step's original Core results, evaluated call by call; the record is a
  specification from the plan, the input and Core, not a measured trace.
  Replay recomputes it.
- Reductions may remove step syntax through the aggregate step reductions,
  which keep the helper count and binding inventory; lower either mask to a
  smaller admitted mask, removing whole canonical guards; replace the
  `counter` or `accumulator` inner bound by the `input` bound; and move the
  input to a boundary input. Every candidate is sealed by the full checker and
  must be strictly smaller than its parent in nodes, then literal weight.
- Fixed corpus coverage: every aggregate step AST feature that the
  `runtime-loops` corpus requires, one to three helpers, all four aggregate
  templates, all six boundary inputs, all twelve generation shapes, outer
  iteration counts 0 to 3, inner trip counts 0 to 3 within a run outer
  iteration, and total step calls 0, 1, 2, 3, 4, 6 and 9.

The registered Lean test requires that the unrolled reference returns the
accumulator of the call-by-call specification for 1,020 generated cases, that
generation draws all twelve shapes and replays exactly, that tampering with a
mask, the bound or the recorded iterations is refused, and that reductions
lower a mask, replace the bound and stay strictly smaller; the revision-four
and emitter-feature tests include the profile. Over the first 256 functions
accepted from seed 1 under revision four, generation took 1.13 attempts per
function, excluding 30 boundary identities and 4 step template budgets, with
256 distinct sources and every shape 12 to 29 times. The fixed corpus has one
plan per shape at all six inputs, 72 cases, and requires all 39 step features
its cases use, the loop corpus's 37 with `and` and `==`; its validator
recomputes the outer trips, the input and counter bounds and the first
accumulator bound. Frozen matrices matched every case on O0, O2 and Yul: the
fixed corpus with complete coverage in 118, 114 and 162 seconds, and random
suites of four whole functions, 40 cases, in 52, 47 and 65 seconds.

**Bounded recursion.** The second new program shape is `runtime-recursion`: a
source function that calls itself, or two functions that call each other, to
a depth taken from the input, over an aggregate step. Before any code, a probe
compiled three recursive sources with the pinned compiler and std, exported
checked Hull, built Sonatina O0, O2 and Yul code images, and ran them on Anvil
and on the Lean Hull runner: self-recursion, mutual recursion and recursion
with work after the call matched a model of the function at eight inputs on
every path. Original Core needs no recursion and no shared runtime code or
proof changes. The existing profiles, corpora, emitters and emitter proofs stay
unchanged, and this emitter has no proof yet. The definitions were fixed before
execution:

- Step: an aggregate step DAG of one to three helpers, generated with the
  current G0 revision as for `runtime-loops`, so revision four equals revision
  three.
- Recursion forms. With input `x`, depth mask `D` and depth `d = x & D`, the
  contract returns `f(d, x)`, where each call with `d > 0` makes exactly one
  call at depth `d - 1` and `f(0, acc) = acc`:
  - `tail`: `f(d, acc) = f(d - 1, step(acc))`;
  - `nontail`: `f(d, acc) = step(f(d - 1, acc)) + d`, so each frame's own work
    and depth follow the inner call;
  - `mutual`: `even(d, acc) = odd(d - 1, step(acc))` and
    `odd(d, acc) = even(d - 1, acc + d)`, two functions calling each other,
    entered at `even`.

  Each function's single result local is assigned in both branches of one
  `if`.
- Bounds: plans admit depth masks 0, 1, 3 and 7; generation draws 1, 3 or 7.
  A call therefore recurses at most seven frames deep, with at most seven step
  calls (four in `mutual`).
- The original Core reference unrolls the frames into at most seven ordinal
  guards over one accumulator cell, with no recursion and no counter:
  - `tail` applies the step at ordinals 0 to `d - 1`;
  - `nontail` applies `step(acc) + k` for `k` from 1 to `d`, innermost frame
    first;
  - `mutual` applies the step at even ordinals `i < d` and `acc + (d - i)` at
    odd ones.

  It is checked by the full Core checker and the 512-node case limit.
- Shapes: the nine combinations of form and generation mask, drawn from a
  SplitMix64 hash of the case seed, independent of the step's helper count and
  template.
- Boundary inputs: 0, 1, 2, 3, 7, `2^256 - 1` and `2^255`, giving depths zero to
  three and seven under mask seven and an even positive depth for `mutual`.
  Random campaigns add the four seeded inputs.
- Exclusions, in order:
  - a node budget too small for the shape or above 512;
  - the step's own generation exclusions;
  - a step whose four boundary inputs return the same Word;
  - fuel exhaustion on a boundary input, an inconclusive resource exclusion;
  - a function that returns every boundary input unchanged
    (`boundary-identity`).

  A depth-zero input returns itself, so the last rule requires some input that
  recurses to change; the profile needs no acceptance filter.
- Specified depths: a case's depth is `x & D`, prescribed by the plan and the
  input, not a measured trace.
- Reductions:
  - shrink the step through the aggregate step reductions, which keep the
    helper count and binding inventory;
  - lower the depth mask, removing whole guards;
  - replace `nontail` or `mutual` by `tail`;
  - move the input to a boundary input.

  Every candidate is sealed by the full checker and must be strictly smaller
  than its parent in nodes, then literal weight.
- Fixed corpus coverage:
  - every aggregate step AST feature its cases use, at least the loop corpus's
    37;
  - one to three helpers and all four aggregate templates;
  - all seven boundary inputs;
  - all nine generation shapes;
  - depths 0, 1, 2, 3 and 7.

The registered Lean test compares the unrolled reference with a recursive
model of the emitted source, evaluated frame by frame over the step's original
Core, for 1,023 generated cases. It also requires that generation draws all
nine shapes and replays exactly, that tampering with the mask or the form is
refused, and that reductions lower the mask, fall back to `tail` and stay
strictly smaller. The revision-four and emitter-feature tests include the
profile.

Over the first 256 functions accepted from seed 1 under revision four,
generation took 1.04 attempts per function, excluding 11 boundary identities,
with 256 distinct sources and every shape 20 to 36 times. The fixed corpus has
one plan per shape at all seven inputs, 63 cases. It requires all 39 step
features its cases use: the loop corpus's 37 with `and` and `==`.

Frozen matrices matched every case on O0, O2 and Yul:
- the fixed corpus, with complete coverage, in 115, 105 and 144 seconds;
- random suites of four whole functions, 44 cases, in 61, 59 and 77 seconds.

**Inline Yul.** The third new program shape is `runtime-assembly`: the
functions of `runtime-primitives`, rendered partly or wholly as inline Yul in
`assembly { }` blocks. Every earlier source used Solcore expressions and
statements only; the pinned std's opcode wrappers are the only inline Yul the
compiler had seen.

Before any code, a probe compiled five sources with the pinned compiler and
std and ran them on every path: checked Hull export, Sonatina O0 and O2 code
images, Yul through `export-rust-yul.py` and the pinned solc, Anvil, and the
Lean Hull runner. The sources covered:
- every pure Word builtin used below;
- Yul `let`, `switch` with `case 0` and `default`, `if`, nested blocks, a
  `for` loop and a Yul function;
- assignments of Solcore Word locals and reads of locals and parameters from
  Yul, several `assembly` blocks in one function and in a helper;
- 256-bit decimal and hexadecimal literals.

All of them matched a model of EVM word semantics at ten inputs on every path.
Core, the Hull runner, both EVM backends and `export-rust-yul.py` need no
change, and no shared runtime code or proof changes. The existing profiles,
corpora, emitters and emitter proofs stay unchanged, and this emitter has no
proof yet. The definitions were fixed before execution:

- Core: the `runtime-primitives` function of the case seed, generated by the
  same steps (the G0 program under the current revision and swarm mask, then
  one Word literal abstracted to the input), so the original Core reference is
  unchanged. A registered test requires the two profiles' functions to agree
  for the same seed, budget and revision.
- Renderer coverage, its `featureSupport` under revision four: all 26 G0
  features, so revision four equals revision three for this profile.
  - Word literals become decimal Yul literals and Bool literals 1 or 0.
  - Locals are read by name.
  - `let` becomes Yul `let`.
  - Builtins render the operations: `not`, `clz`, `iszero` (for `!`), `add`,
    `sub`, `mul`, `div`, `mod`, `and`, `or`, `xor`, `eq`, `gt`, `sgt`,
    `shl`, `shr` and `sar` (shift first), `byte`, `exp`, `signextend`,
    `sdiv`, `smod`, `addmod` and `mulmod`.

  Comparisons yield the Words 0 and 1 that Core's Bools correspond to.
- How Solcore and Yul mix: one of three forms per function, drawn from a
  SplitMix64 hash of the case seed and recorded in the case's plan:
  - `switch`: the whole body is one `assembly` block assigning the Solcore
    result local. Core `if` becomes `switch` with `case 0` for the else branch
    and `default` for the then branch, assigning a Yul local in each.
  - `if`: the whole body as in `switch`, with each Core `if` as a Yul local
    holding the condition and two Yul `if`s, on it and on `iszero` of it.
  - `operations`: Solcore `let`, `if`, literals and `!`, as in the primitive
    renderer, with every other operation in its own `assembly` block. The
    block assigns a fresh Solcore Word local from Solcore Word operands, and a
    comparison's Word becomes a Bool through std's `tobool`.

  Yul never reads a Bool, and no helper or call is involved: the primitive
  functions have none.
- Boundary inputs: the primitive profile's eight; random campaigns add the four
  seeded inputs.
- Exclusions: those of `runtime-primitives`, in its order. The identity filter
  `exclude-boundary-identity-v1` applies, since a primitive function can be
  the identity.
- Reductions: the primitive reductions of the Core function (G0 shrinking
  under the abstraction and smaller inputs), sealed by the full checker and
  strictly smaller. Every reduction keeps the parent's form, which changes no
  Core node.
- Fixed corpus coverage: every one of the 29 G0 AST features that the primitive
  corpus requires, in each of the three forms, and all eight boundary inputs.

The profile was implemented at `33d7c411d`:
- `AssemblyRenderer`, `AssemblyEmitter` and `AssemblyCases`, the case-tool
  commands `assembly-generate` and `assembly-emit`, and campaign and suite
  registration.
- A registered Lean test requires both profiles to accept the same functions,
  with the same programs, inputs, observations, generation records and
  exclusions, under revisions one, three and four, both input selections and
  both acceptance filters. It also checks each form's source against a golden
  text.
- The fixed corpus is the primitive corpus's 34 distinct functions in three
  consecutive groups, each combined by a balanced XOR tree, in each form at the
  eight boundary inputs. That gives 72 cases from nine plans, with every
  feature in every form.

Two other corpora were rejected:
- the 81 primitive cases in each form (243 cases, 102 sources), which needed
  more than the suite's 900-second profile limit on Yul;
- generated functions chosen for coverage, which crashed Sonatina O0
  code-image export in four of 17 whole-body functions.

Each of those four crashes shifts by a constant count of at least 2^64. The
crash is recorded in the local questions file without investigation, and the
corpus avoids that construct, so that it does not track a known upstream
defect; random campaigns still generate it.

Frozen matrices at `33d7c411d`:
- the fixed corpus matched all 72 cases on O0, O2 and Yul with complete form,
  feature and input coverage, compiling 8 sources, in 114, 109 and 135
  seconds;
- random suites from root seed 1 with eight whole functions, 96 cases from 8
  sources in all three forms, matched all 96 on O2 in 127 seconds. On O0 and
  Yul, 84 matched and the twelve inputs of one `switch` function crashed
  Sonatina O0 code-image export, in 203 and 261 seconds. The crash is
  retained as a finding.

**Composed control flow.** Each earlier pure profile exercises one control
construct in isolation. Two new profiles compose them, so that compiler
lowering meets the constructs together:
- `runtime-loop-closures`: a closure created in a bounded loop body, capturing
  a loop-carried Word local and applied in the same iteration;
- `runtime-recursive-loops`: a bounded loop inside every frame of the three
  `runtime-recursion` forms.

One profile per composition keeps each plan, reference and reduction set to
those of the profile it extends, where one profile with a recorded composition
kind would carry two unrelated plan shapes.

Before any code, a probe compiled six sources with the pinned compiler and std
and ran them on every path: checked Hull export, Sonatina O0 and O2 code
images, Yul through `export-rust-yul.py` and the pinned solc, Anvil, and the
Lean Hull runner. The sources were:
- three loops whose body creates a closure: with `let`, capturing the
  accumulator and changed before the call; reassigned to a variable declared
  before the loop, capturing the counter and called through a generic
  function; and applied twice in its iteration over a step with a helper;
- tail, non-tail and mutual recursion with a while loop in every frame, its
  trip count read from the frame's depth.

All of them matched a model of the source at ten inputs on every path. Core,
the Hull runner, both EVM backends and `export-rust-yul.py` need no change,
and no shared runtime code or proof changes. The existing profiles, corpora,
emitters and emitter proofs stay unchanged; the two emitters have no proof
yet. The definitions were fixed before execution:

- Step, for both: an aggregate step DAG of one to three helpers, generated
  with the current G0 revision exactly as for `runtime-loops`, so every G0
  feature renders and revision four equals revision three. The default budget
  is 384 nodes, and the complete applied program is checked against the
  512-node case limit.
- `runtime-loop-closures` source. With input `x` and mask `m`, the wrapper
  sets `acc = x` and runs `x & m` iterations with a counter `c` from zero, as
  `runtime-loops` does. Every iteration creates a fresh closure with `let`,
  in one of two captures fixed per plan:
  - `accumulator`: `f(a) = step(acc + a)`; the body then sets `acc = acc + 1`
    and `acc = f(c) + acc`, so the closure must hold the snapshot taken
    before the change;
  - `counter`: `f(a) = step(a) + c`; the body then increments `c` and sets
    `acc = sc_apply(f, acc)` through the generic apply function of
    `runtime-closures`, so the closure must hold the counter before its
    increment.
- `runtime-recursive-loops` source. With input `x`, depth mask `D` and inner
  mask `I`, the wrapper calls the form's entry with depth `d = x & D` and
  `acc = x`, as `runtime-recursion` does. Every frame with depth `e > 0` runs
  a while loop of `e & I` iterations, with its trip count, counter and value
  declared in the frame:
  - `tail`: the loop applies the step to `acc`, then the frame calls depth
    `e - 1` with the result;
  - `nontail`: the frame first calls depth `e - 1`, then loops the step over
    the result and adds `e`;
  - `mutual`: `sc_even` loops the step before calling `sc_odd`, and `sc_odd`
    loops `v = v + e` before calling `sc_even`.
- Bounds. Loop closures admit masks 0, 1, 3 and 7 and generate with 1, 3 and
  7: at most seven iterations, each creating and calling one closure. Recursive loops
  admit masks 0, 1 and 3 for both and generate with 1 and 3: at most three
  frames, three iterations in a frame and six in a call.
- Core references, both finite, with no loop, recursion or counter cell:
  - loop closures unroll literal ordinal guards over one accumulator cell, as
    `runtime-loops`. Each run guard builds a Core lambda over an immutable
    Word snapshot (the loaded accumulator or the ordinal itself) and applies
    it, directly or through the Core instantiation of the generic apply
    function at Word;
  - recursive loops unroll the frames into ordinal guards, as
    `runtime-recursion`. Each run frame binds its trip count and unrolls
    inner ordinal guards, as `runtime-nested-loops`.
- Shapes, from a SplitMix64 hash of the case seed so that consecutive seeds
  vary in shape independently of the step: the six combinations of capture
  and mask, and the twelve combinations of form, depth mask and inner mask.
- Boundary inputs: 0, 1, 3, 7, `2^256 - 1` and `2^255` for loop closures
  (zero to seven iterations), and 0, 1, 2, 3, `2^256 - 1` and `2^255` for
  recursive loops (depths zero to three); random campaigns add the four
  seeded inputs.
- Exclusions, in order: a node budget too small for the shape or above 512,
  the step's own generation exclusions, a step whose boundary inputs return
  the same Word, and fuel exhaustion on a boundary input (an inconclusive
  resource exclusion). Then:
  - loop closures exclude a function whose positive-trip boundary inputs all
    return themselves, as `runtime-loops`;
  - recursive loops exclude a function that returns every boundary input
    unchanged (`boundary-identity`), as `runtime-recursion`.

  A zero-trip or depth-zero input returns itself, so these rules already ask
  some changed input, and neither profile takes the identity filter.
- Reductions: the aggregate step reductions, which keep the helper count and
  binding inventory; a smaller admitted mask, removing whole canonical guards;
  for recursive loops, the `tail` form in place of `nontail` or `mutual`; and
  the input moved to a boundary input. Every reduction keeps the capture, and
  every candidate is sealed by the full checker and strictly smaller in nodes,
  then literal weight.
- Specified iterations, from the plan and the input, never a measured trace:
  `x & m` for loop closures, and for recursive loops the depth and the sum of
  `e & I` over the frames.
- Fixed corpus coverage, for each profile: every aggregate step AST feature
  that the `runtime-loops` corpus requires, one to three helpers, all four
  aggregate templates, all six boundary inputs and every generation shape.
  Loop closures also need iteration counts 0, 1, 3 and 7; recursive loops
  need depths 0 to 3 and total iterations 0, 1, 2, 3 and 6.

Both profiles were implemented at `479eba68b`, with the definitions above:
- `LoopClosure` and `RecursiveLoop` Core plans, emitters and cases modules,
  four case-tool commands, and campaign and suite registration;
- registered Lean tests that compare each unrolled reference with a model of
  the emitted source, over the step's original Core, for 1,020 generated cases
  of each profile;
- fixed corpora of eight loop-closure functions (48 cases) and thirteen
  recursive-loop functions (78 cases) from G0 revision one, chosen as the
  first seed of each shape and then the seeds covering the most missing step
  features, helper counts and templates.

The `mutual` reference equals the `tail` one when no `sc_odd` frame runs an
iteration (depth mask one, or inner mask zero), so a `tail` reduction there is
not strictly smaller.

Frozen matrices at `479eba68b` matched every case on O0, O2 and Yul:
- the fixed corpora with complete coverage: loop closures in 92, 85 and 118
  seconds and recursive loops in 146, 142 and 197 seconds;
- random suites from root seed 1 with eight whole functions per profile, 80
  cases each: loop closures in 120, 114 and 152 seconds and recursive loops in
  120, 115 and 154 seconds, each generated in two case-tool requests after an
  output-limit retry.

**Inline Yul loops and functions.** `runtime-assembly` renders straight-line
primitive functions inside `assembly` blocks, so no generated case had a Yul
`for` loop or a Yul `function` definition. The Yul front end lowers
loop-carried Yul variables, `break`, `continue`, `leave`, function scopes and
multiple return values on its own path, apart from Solcore's lowering. One new
profile, `runtime-assembly-loops`, renders a whole `runtime-call-graph-loops`
plan as one `assembly` block: the loop as a Yul `for` loop and the step's one
to three helpers as Yul functions. Both constructs then share one plan, one
reference and one reduction set, those of the profile it renders, where a
profile per construct would split the same call-graph loop plan in two.

Before any code, a probe compiled six sources with the pinned compiler and std
and ran them on every path: checked Hull export, Sonatina O0 and O2 code
images, Yul through `export-rust-yul.py` and the pinned solc, Anvil, and the
Lean Hull runner. All six were one `assembly` block in `run`:
- a `for` loop bounded by its condition, one exited by `break` from a
  constant condition, one skipping iterations with `continue` under a
  condition that calls a zero-argument function, one inside a two-argument
  function exited by `leave`, and one with empty init and post blocks whose
  body assigns both results of a two-argument, two-return step function;
- helpers called from each loop body, helpers calling earlier helpers, a Yul
  `switch` in the body, and `let` declarations inside the body;
- functions with zero, one and two arguments and one or two return variables,
  `leave` in nested conditionals, and `let a, b := f(x)` and `a, b := f(x)`.

All of them matched a model of the source at twelve inputs on every path.
Core, the Hull runner, both EVM backends and `export-rust-yul.py` need no
change, and no shared runtime code or proof changes. The existing profiles,
corpora, emitters and emitter proofs stay unchanged, and this emitter has no
proof yet. The definitions were fixed before execution:

- Core: the `runtime-call-graph-loops` plan of the case seed, generated by
  the same steps (the mask, then the directly generated scalar call-graph
  step), so the original Core reference is unchanged: the bounded-loop plan's
  finite ordinal guards over one accumulator cell, with the helpers as
  let-bound Core lambdas in declaration order. Core has no loop, counter,
  second result or early return here. A registered test requires the two
  profiles to agree for the same seed and budget on plans, programs, inputs,
  observations, generation records and exclusions, under both input
  selections.
- Yul rendering, in every form:
  - each helper is a Yul function `sc_fn<k>(sc_arg) -> sc_ret`, defined at
    the top of the block in declaration order;
  - expressions render as in the `switch` form of `runtime-assembly`: the same
    builtins and literals, Yul `let` for Core `let`, and `switch` with
    `case 0` for the else branch and `default` for the then branch;
  - a call is `sc_fn<k>(argument)` inside its expression;
  - Yul temporaries are numbered across the whole block, so no name is
    declared twice;
  - with input `x` and mask `M`, the block sets `sc_out`, which `run`
    returns. The wrapper is `run(uint256)` of `SynthesizedAssemblyLoops`.
- Forms, one per plan:
  - `for`: `sc_limit := and(x, M)` and `sc_acc := x` before
    `for { let sc_i := 0 } lt(sc_i, sc_limit) { sc_i := add(sc_i, 1) }`.
    The step's entry is inlined in the body, ending with `sc_acc := value`.
  - `break`: as `for` with condition `1`; the body starts with
    `if iszero(lt(sc_i, sc_limit)) { break }`.
  - `continue`: as `for` with condition `lt(sc_i, sc_bound())`, where the
    zero-argument `sc_bound()` returns `M`; the body starts with
    `if iszero(lt(sc_i, sc_limit)) { continue }`, so the loop runs `M` times
    and skips the step after `sc_limit`.
  - `leave`: the loop is in `function sc_loop(sc_acc, sc_limit) -> sc_ret`,
    which sets `sc_ret := sc_acc` and runs the `break` loop over `sc_ret`
    with `leave` in place of `break`; the block sets
    `sc_out := sc_loop(x, and(x, M))`. A helper's conditional in tail
    position becomes `if condition { then branch, leave }` followed by its
    else branch, so helpers also return through `leave`.
  - `pair`: each helper returns its result and its argument
    (`-> sc_ret, sc_aux`), and every call binds both with
    `let a, b := sc_fn<k>(argument)` and uses the first. The entry is the body
    of `function sc_iterate(sc_arg, sc_count) -> sc_ret, sc_next`, which also
    sets `sc_next := add(sc_count, 1)`. The counter is declared before
    `for { } lt(sc_i, sc_limit) { } { sc_acc, sc_i := sc_iterate(sc_acc, sc_i) }`.

  Every accepted step's entry calls a helper (an exclusion below), so in the
  four inline forms a helper is called from inside the loop body, and in
  `pair` from the function that the loop body calls.
- Shapes: the form comes from a SplitMix64 hash of the case seed (domain
  `0x61736d6c6f6f7001`), so that consecutive seeds vary in form independently
  of the plan, and is recorded in the plan and the generated origin. With the
  generated masks 1, 3 and 7, that gives fifteen shapes.
- Bounds: masks 0, 1, 3 and 7 admitted, at most seven iterations; the default
  budget is 256 nodes, as for `runtime-call-graph-loops`, the minimum 39, and
  the complete applied program is checked against the 512-node case limit.
- Boundary inputs: 0, 1, 3, 7, `2^256 - 1` and `2^255` (zero to seven
  iterations); random campaigns add the four seeded inputs.
- Exclusions: those of `runtime-call-graph-loops`, in its order: a budget too
  small for the mask or above 512, the step's own generation exclusions, an
  entry without a helper call, a step whose eight primitive boundary inputs
  return the same Word, fuel exhaustion on a boundary input (an inconclusive
  resource exclusion), and a function whose positive-trip boundary inputs all
  return themselves. A zero-trip input returns itself and the last rule asks
  for a changed positive-trip input, so the identity filter does not apply.
- Reductions: those of `runtime-call-graph-loops`: the typed call-graph
  reductions, which keep the helper count and binding inventory; a smaller
  admitted mask, removing whole canonical guards; and the input moved to a
  boundary input. Every reduction keeps the parent's form, and every candidate
  is sealed by the full checker and strictly smaller in nodes, then literal
  weight. A reduced origin records the parent plan and input.
- Specified iterations, from the plan and the input, never a measured trace:
  `x & M`.
- Fixed corpus coverage: the fifteen shapes; every form at iteration counts 0,
  1, 3 and 7; masks 1, 3 and 7; and, as for `runtime-call-graph-loops`, the 30
  step AST features its corpus requires, one to three helpers, the nine call
  shapes and the six boundary inputs. The corpus is generated with the default
  budget from seed 1 upwards: the first seed of each shape, then the seeds
  covering the most missing step features, helper counts and call shapes until
  nothing is missing, each function at all six inputs.
- The fixed corpus skips steps that shift by a constant count of at least
  2^64, the construct of the recorded Sonatina O0 crash: every shift count
  must read its function's parameter, through lets or calls, or be a literal
  below 2^64. Random campaigns still generate such steps, and any new crash
  goes only to the local questions file.

The profile was implemented at `899c6f284` with the definitions above:
- `AssemblyLoopRenderer`, `AssemblyLoopEmitter` and `AssemblyLoopCases`, the
  case-tool commands `assembly-loop-generate` and `assembly-loop-emit`, and
  campaign and suite registration;
- a registered Lean test that requires both profiles to agree on plans,
  programs, inputs, observations, generation records and exclusions at
  budgets 128, 256 and 384 and under both input selections, checks each form's
  source for a fixture plan against a golden text and its Core reference at
  zero to three iterations, and draws all fifteen shapes in 1,020 generated
  cases;
- a fixed corpus of the first seed of each shape, 15 functions and 90 cases.
  Those already covered every required feature, helper count and call shape,
  so no further seed was added.

The first frozen fixed run at `899c6f284` matched all 90 cases on O0 (140
seconds) and Yul (186), but on O2 the six inputs of seed 15's `pair` plan
crashed code-image export with `Integer overflow when casting to usize`. Its
helper shifts by a Yul local that a `switch 0` assigns the complement of a
large literal, so the count is constant once O2 folds the literal condition;
the shift rule above had counted a conditional as reading the parameter when
either branch did. The corpus was rebuilt at `d59753e12` by the same
selection with a rule that follows constants through lets, conditionals and
calls: a conditional may fold when both branches may, or when its condition
and one branch may, and a call when the callee's result may for its argument.
That replaced three seeds (`1:continue`, `1:pair` and `7:pair`); 403 of the
757 plans accepted from seeds 1 to 3,000 pass it.

Frozen matrices, with the same scripts and binaries at both commits (the
freeze digest did not change):
- At `d59753e12` the fixed corpus matched all 90 cases on O0, O2 and Yul with
  complete shape, form-iteration, mask, feature, helper, call-shape and input
  coverage, compiling 15 sources, in 183, 154 and 192 seconds, under load
  averages of 9 to 31 from other work on the machine.
- Random suites at `899c6f284` from root seed 1 with eight whole functions
  took 22 attempts in one case-tool request, excluding 14 plans (nine entries
  without a helper call, three steps whose boundary outputs agree and two
  whose positive-trip inputs all returned themselves). They drew 80 cases
  from 8 sources, all five forms in seven shapes, iteration counts 0 to 3 and
  5 to 7 and all nine call shapes.
- On each of O0, O2 and Yul, 70 matched and the ten inputs of the eighth
  function (`continue`, mask 7) crashed code-image export with the same
  message, in 177, 171 and 308 seconds. Its reduction kept the fingerprint
  with a literal shift count of 2^255. The crash is retained as a finding and
  recorded locally without investigation, so the three random gates did not
  pass.

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
`SSTORE` address computed slots.

`EventLog.emit_source_meaning` covers the `stateful-logs` emitter and the logs
a transaction commits. Its method takes flags and an input, runs the two-slot
storage protocol and reserves a 64-byte buffer from the free-memory pointer at
offset 64. It then runs up to three static log sites. A site whose guard bit is
set applies the step to the result plus its guard, writes zero to two data
Words to the buffer and emits a log with zero to four topics through the
`std.opcodes` wrapper `log0` to `log4`. Odd flags then revert with the result.
The log grammar extends the rollback one with the store `mstore(o, v);` and a
guarded log block. Its meaning adds a memory, known word by word, and puts the
emitted logs in the outcome; a revert discards the logs with the writes. The
theorem holds for every memory whose word at offset 64 is known and points to a
buffer below `2^256`. The Core reference writes each log as a frame of word
logs under `EventLog.framingVersion`. The theorem states that the committed
journal is the framing of the source logs, in order and from the target, and
that it is empty on revert. The event-log wrapper's private Core definitions
were made public in a visibility-only commit, and a named copy of the
aggregate helper-loop lemma admits the wrapper aliases in front of the raw
aliases; no existing statement changed. The new assumptions are the parsing of
the site blocks and wrapper calls, the `MLOAD`, `MSTORE` and `LOG0` to `LOG4`
meaning of the wrappers, the free-memory pointer that `std.dispatch` leaves at
offset 64, and that a revert discards logs. The other emitters that render
with the aggregate renderer (closures, comptime, modules, storage mappings,
sender-keyed ledgers, dynamic arrays, dynamic bytes, long bytes, call value,
calls and forwarded value) are not covered; their texts use forms outside the
source fragments.

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
key one. The registered `SourceLogMeaning` test runs the three golden histories,
25 regression plans over five site layouts, fourteen raw primitive steps and 16
generated scenarios from three storages and three buffer pointers, 64 and
`2^256 - 64` among them. All 3,474 transactions settle as Core, and the 2,394
committed logs are the framing of the source logs and decode to them. Altered
pointers, stores, sizes and topic counts lose or change the meaning. The full
Lean build (10,120 jobs), registered tests and the semantic-kernel policy
passed.

**State and ABI:** expand from the existing two-slot, Word-input and bounded
call profiles to selected dynamic ABI values and richer account/storage or
transaction behaviors. Define committed observations, rollback, deployment and
sequence reduction before enabling each feature. Gas-sensitive equivalence,
precompiles and arbitrary external accounts require separate explicit scopes.
The transaction counts in the profile definitions below are those of fixed
corpora and imported scenarios; random campaigns now generate up to eight
transactions, as defined under **Longer random transaction sequences**.

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

The tenth extension, `stateful-nested-array`, adds one nested dynamic ABI
input. It changes inputs only: original Core reads calldata directly, so the
contract runtime is unchanged. A probe compiled a contract with a
`calldata<array<calldata<array<uint256>>>>` parameter, the dialect's
`uint256[][]`, at O0 and O2. Hull and the EVM agreed on its status, payload
and slots for ragged rows, an empty row and an odd-flags revert. Its
definitions were fixed before execution:

- Transactions: one to three zero-value calls of `run(uint256 flags,
  uint256[][] values)` with the canonical nested head/tail encoding. That is
  the flags, the head offset 64, the outer length, one offset per row relative
  to the start of that offset table, then each row's length and elements. A
  value has at most three rows of at most two elements each. Other encodings
  are outside the scope.
- Effects: for each present row `i` and each present element `j` of it, the
  accumulator, starting from slot zero, becomes `step(accumulator +
  values[i][j])` and is written to slot `1 + 2i + j`. Then the accumulator
  goes to slot zero, the running row count plus the outer length to slot seven
  and the running element count plus the number of elements to slot eight. The
  result rereads slots zero, seven and eight; odd flags revert with it after
  the writes.
- Committed observations: status, payload and slots zero through eight after
  every transaction on all three paths. The Hull and EVM paths must show no
  nonzero committed slot outside them.
- Protocol: odd flags revert, and a revert keeps the nine slots. A returned
  transaction adds its row count to slot seven and its element count to slot
  eight, and returns the sum of slots zero, seven and eight.
- Rollback and deployment: as for the dynamic-array profile.
- Sequence reduction: checked step reduction, transaction removal with stable
  IDs, removal of one row, removal of one row's last element, zeroed elements,
  and flags reduced to their parity or with the revert bit cleared. Candidates
  are ordered by transaction count, program complexity, the total number of
  rows and elements, then flags and elements.
- Node budget: the row and element guards are a fixed part of the wrapper.
  Like the long-bytes chunk guards, they lie outside the step's node budget.

Original Core reads the head offset, the outer length, each present row's
offset and length and each present element with `inputDataWordBE?`, so Core,
its hosts and the contract runtime are unchanged. The source reads the same
Words through the lazy calldata view. The adapter, campaign and suite add the
profile as a twenty-seventh suite profile with one new native tool; the
twenty-one other native tools are byte-identical to main's. The row and
element guards (270 nodes) lie outside the step budget, so generation reserves
the measured 86-node wrapper. All 300 of the first 300 seeds at 384 nodes were
accepted, and their 900 transactions used every outer and row length. A case
reaches about 73 KB, so a native shrink response carries at most 32
candidates. The fallback, a static multi-word element beside a dynamic one,
was not needed.

The fixed corpus has twelve scenarios (eight imported, four generated) and 33
transactions. Its histories were computed outside Lean by a separate evaluator
of the step programs and a direct model of the protocol. A registered Lean
validator confirmed every status, payload and slot against original Core and
rejected tampered entries. Coverage includes all 32 step features of the
corpus, the six boundary Words as elements, one to three helpers and
transactions, four templates, both outcomes, six completion patterns, outer
lengths 0 to 3 and row lengths 0 to 2. The calldata of all 33 fixed and 48
random transactions matched `cast calldata`.

The full Lean build (10,113 jobs), registered tests, kernel policy and 538
Python policy tests passed. The fixed suite matched all 12 scenarios and 33
prefixes on Sonatina O0 and O2 (93.8 and 91.0 seconds). Random seed
`20261026`, sixteen cases and 2,048 attempts accepted sixteen scenarios from
sixteen attempts with no exclusions. Both levels matched all sixteen and 48
prefixes (166.1 and 163.6 seconds), covering every outer and row length, with
reverts at outer lengths 0 to 3. Neither random run produced a finding.

A copied Hull difference in slot 6, which only a third row with two elements
writes, at the first of three transactions was reduced on each level to that
transaction with an empty outer array and a reduced step: seven accepted
reductions in nine actual candidate executions. Original and reduced archives
replayed exactly with agreement (four replays), and synthetic fingerprints
reproduced. Core or Hull fuel one was inconclusive. With the extended storage
and suite scripts, the storage, rollback, call, keyed, dynamic-array, log,
call-value, bytes, forwarded-value, mapping, ledger and long-bytes fixed
corpora still matched all 155 scenarios and 427 prefixes on both levels. An
offline preparation of the worktree's cloned cache verified all twenty-two
native tools as ready. Hosted CI has not been run.

This scope does not compare deeper nesting, static or multi-word elements,
more than three rows or two elements per row, non-canonical offsets, truncated
input or the decoder's revert paths, multi-word return values, gas, balances,
nonces, code or memory. Agreement is test evidence, not a preservation proof.

**Whole committed storage.** The comparisons above observe declared slots on
all three paths, and nine profiles add Hull/EVM containment of undeclared
slots. A miscompiled write outside the declaration, or a stray write by the
original Core contract itself, was therefore invisible on at least one path.
All thirteen stateful profiles now also compare the observed accounts' whole
committed storage after every transaction. The definitions were fixed before
execution:

- Observed accounts: every contract the profile deploys. That is the one
  contract of the eleven storage-family profiles (role `contract`) and the
  parent and child of `stateful-calls` and `stateful-forwarded-value`.
  Senders, precompiles and other accounts are not observed. On the EVM path a
  storage change at any other account fails closed as an adapter error, as
  the declared-slot profiles already did.
- Enumeration on original Core: the committed world after deployment (the
  declared post-deployment world) and after every transaction (the terminal
  `finalWorld`, or the prior world when a transaction is incomplete). Core's
  function-valued account storage could not be enumerated, so `Account` now
  also keeps the strictly increasing list of exactly its present slots, which
  every storage write maintains. `Account.storageEntries` lists each present
  slot with its value. A theorem states that an entry is listed exactly when
  `storageValue?` returns it, and `Account.ext` still holds. All existing
  storage laws are unchanged.
- Enumeration on imported Hull: each observed account's committed storage
  entries after deployment and after every call. A revert or an incomplete
  call keeps the prior entries. The runner canonicalizes them: every distinct
  key with the value the entries' lookup selects, zero values dropped, in
  increasing slot order.
- Enumeration on the EVM: the union of the observed accounts' storage keys
  that `debug_traceTransaction` with `prestateTracer` in diff mode reports for
  the deployment transactions and every mined transaction so far. Every key is
  reread with `eth_getStorageAt` at each receipt block. A new contract starts
  with empty storage, so a slot is nonzero after a block only if some
  transaction up to it changed that slot. A probe on Anvil 1.5.1 found that
  the diff reports exactly the slots whose committed value a transaction
  changes. It covered constructor writes, fresh, changed and cleared slots,
  slots 0, 2^255 and 2^256 - 1, values restored by a later transaction,
  reverted transactions, and child calls that returned or reverted under a
  returned or reverted parent. Writes that leave a value unchanged inside one
  transaction are not reported: 0 to 5 to 0, 3 to 4 to 3, same-value writes,
  and writes rolled back with a frame. The opcode trace shows that those
  writes ran, but committed storage cannot observe them. The probe's final
  `anvil_dumpState` held exactly the storage the reported changes imply, and
  `scripts/check-evm-storage-diff.py` repeats the probe. Anvil 1.5.1 lacks
  `debug_storageRangeAt`. The first matrix also compared `anvil_dumpState`
  after deployment and every mined transaction. Under `--steps-tracing` the
  dump embeds every transaction's step trace, so on the nested-array corpus
  it outgrew its 64 MiB bound within two transactions and failed four O0
  scenarios closed as adapter errors; longer sequences would also exceed the
  4 MiB RPC output limit. That run-time cross-check was dropped, and only the
  probe keeps it.
- Zero and absent are equal. Observations list only nonzero values, and
  writing zero removes an entry on every path, so no observation distinguishes
  a cleared slot from one never written.
- Comparison and classification: after deployment, every path's observed
  storage must be empty, because every profile has an empty constructor.
  After every transaction the three observations must be equal. A difference
  is a `semantic-mismatch` at the existing stage (`initial-storage` or
  `initial-accounts` for deployment, else the transaction) with the field
  `accountStorage`. It is classified by `accountStorageDifferences`: sorted,
  unique records of the account role, the slot and the paths at which the slot
  is zero. The slot is its decimal Word if the case declares it (its observed
  slots) and `undeclared` otherwise. The declared-slot, containment, balance
  and log comparisons are unchanged and still reported.
- Fingerprints: the storage and call campaigns copy `accountStorageDifferences`
  and `accountStorageRollbackPaths` from the comparison into the fingerprint.
  A reduction may move a stray write to another undeclared slot. It cannot
  turn it into a declared-slot difference, or change its account or the paths
  that lack it. Declared slots keep their numbers, as before.
- Rollback and reverts: on every path, a reverted transaction must leave the
  whole observed storage equal to the prior committed observation. In the call
  profiles, a child revert (odd input) under a returned root must leave the
  child's whole storage unchanged. A path that breaks either rule adds
  `accountStorage` and is listed in `accountStorageRollbackPaths`. An
  incomplete transaction reports the prior committed storage, and comparison
  stops there as before.
- Reduction and replay: candidates run with the same observation, and
  `same_failure` requires the whole fingerprint, so reduction preserves the
  new classification. Exact replay recomputes all three observations from a
  fresh deployment. The copied-observation test adapter gains a stray field
  (`stray` for storage profiles, `parent:stray` and `child:stray` for call
  profiles). After actual agreement, it adds value one at the undeclared slot
  2^256 - 2 to one path's observation of the selected transaction. A candidate
  that removes the transaction, or declares or already holds that slot,
  cannot keep the synthetic finding.
- Schemas and versions: the twelve history schemas of the thirteen profiles
  (the two-slot and rollback profiles share one) move from `.v1` to `.v2`.
  They now require `initialAccountStorage`, `accountStorage` on every row and
  `finalAccountStorage`. The storage and call report schemas
  (`semantic-storage-differential`, `semantic-call-differential`) and analysis
  schemas move to `.v2`. Case, plan, corpus, Hull scenario and campaign
  summary schemas are unchanged, so saved cases and fixed corpora stay valid.
  Every native tool and Hull runner is rebuilt, because the Core account
  representation changed and the observers and runners emit the new fields.
  Older archives therefore cannot be replayed exactly; rerun their saved
  cases with `--case`.

Original Core enumerates each account through `Account.storageEntries`. Its
private slot list is proved sorted and exact, the full build passed with only
that runtime change, and every existing storage law and `Account.ext` are
unchanged. `Solcore.Synthesis.Stateful.AccountStorage` renders the observation
for the twelve observers and canonicalizes Hull entries, with exactness and
order theorems. The six Hull runners and both adapters report and compare it,
and the campaigns fingerprint it. Before each commit the full Lean build
(10,132 jobs), registered tests, kernel policy, 572 Python policy tests and
`git diff --check` passed; the three corpus validators passed on the final
code.

With frozen scripts and native tools at the final commit, the fixed corpora of
all thirteen stateful profiles matched on Sonatina O0 and O2: 167 scenarios and
460 prefixes on each level, in 1,004 and 1,011 seconds, with no finding. A
synthetic stray Hull write at `tx-2` of the two-slot `generated-21` scenario,
which no earlier observation could see, was classified as an undeclared slot
absent on Core and the EVM. On each level it was reduced to that transaction
with input zero and a smaller step: sixteen accepted reductions in sixteen
candidate executions. A stray EVM child write at the child-reverting `tx-1` of
`child-rollback-then-value` was classified as an undeclared child slot and a
child-rollback violation on that path. On each level it was reduced to that
transaction with input one: four accepted reductions in seven executions. The
rejected candidates removed the transaction or made the child return, which
drops the rollback classification. Every candidate's actual comparison
matched. The original and reduced archives replayed exactly with agreement
(eight replays), and each replay reproduced the synthetic fingerprint. Hosted
CI has not been run.

This observation does not cover accounts other than the deployed contracts,
transient storage, gas, nonces or code. Agreement is test evidence, not a
preservation proof.

**G0 revision two for stateful steps.** Random stateful campaigns generate the
checked step with
[G0 revision two](../../scripts/SEMANTIC_DIFFERENTIAL.md#g0-generator-revisions)
(`core-g0-v2/lcg64-v1`), as the G0-based pure profiles already do. The
definitions:

- Generation: every stateful case tool's `generate` takes an optional G0
  version after `FUEL`. Without one it keeps revision one, so the corpus
  validators and fixed manifests regenerate their seeds bit for bit. Only the
  step's helper programs depend on the revision; the transaction choices,
  wrappers and protocols are unchanged.
- Record and replay: a case records its version in `generatorVersion`.
  Replay regenerates a generated case's step with that version and rejects a
  case whose recorded version would regenerate a different step, or which
  names an unknown version. Imported plans record revision one.
- Reduction: candidates inherit their parent's recorded version, so a
  reduced revision-two case replays as revision two.
- Campaigns: the storage and call campaigns take `--g0-version`. Random
  generation defaults to revision two; a fixed corpus or saved case uses the
  version it records and refuses a disagreeing explicit one. Summaries record
  `configuration.g0Version` and `generation.generatorVersions`, which the
  fuzzing ledger already reads. The suite needs no change.

With scripts and native tools frozen, the thirteen fixed corpora still pass on
O0 and O2 with 167 scenarios and 460 matched prefixes per level, every profile
recording revision one. A random suite sample of four cases per profile (seed
20261027) passed on both levels with 52 scenarios and 156 prefixes, and every
profile recorded `core-g0-v2/lcg64-v1`. There were no findings.

**Longer random transaction sequences.** Random stateful scenarios had exactly
three transactions. They now take a requested length up to a bound B. The
definitions were fixed before execution:

- Length: generation takes a transaction count from one to B. The default is
  three, which leaves generation, the origin and every fixed corpus unchanged,
  bit for bit. A generated origin records a count other than three as
  `transactionCount`; replay regenerates exactly that length, and a recorded
  count of three is noncanonical.
- Sequence: the first L transactions of consecutive three-transaction blocks.
  Block zero is the profile's existing three transactions from the scenario
  seed. Block k > 0 draws the same choices from its own seed, the high half of
  draw k of a stream seeded with the scenario seed xor `tx-block`. IDs run
  `tx-0` to `tx-(L-1)`. The step, the wrapper and every scenario-level choice,
  such as the deployment value or the log sites, come from the scenario seed
  alone. Every transaction follows its block's prescribed completion, which
  generation validates. The origin's per-transaction lists (indices, parities,
  completions, flags) have L entries, and `sequenceChoices` lists the choices
  of every block used.
- Value bounds: call-value scenarios still send at most 2^72 including the
  deployment value, and a forwarded-value parent forwards at most its 2^72
  endowment in total, so the funded sender and the parent can always pay. A
  generated value or amount that would exceed its total is zero. Three
  transactions never reach either total. The eight-unit `stateful-calls`
  parent sends at most one unit per transaction, so B is at most eight.
- Limits: case decoders, adapters and Hull runners admit one to B
  transactions. Declared-slot runners admit up to 32 observed slots, more than
  the 1 + 2B that a keyed, mapping or ledger sequence declares. Fixed corpora
  and their manifests keep one to three.
- Reduction: the candidates that remove one transaction come first, from the
  last to the first, followed by the existing step, plan and input reductions
  in their order. A tail beyond a finding's first differing transaction is
  then removed before the candidate limit is spent. Each accepted candidate is
  still rerun on all three paths.
- Campaigns: `--transactions` sets the random length, from one to B, and
  defaults to B. A corpus or a saved case keeps its own sequence. Summaries
  record the requested length.
- Time and disk: B is the largest length up to eight whose measured case time
  on O0 and O2, at the suite's default and doubled node budgets, keeps sixteen
  cases well inside the suite's 900-second profile budget and every case well
  inside the 90-second case timeout. The native responses, histories and
  reports of B-transaction cases must stay inside their existing output and
  artifact limits.

B is eight. Suites of four random cases per profile (seed 20261027), run on O0
and O2 in parallel like every matrix here, took at most 9.0 seconds per
eight-transaction case at the 384-node budget and 9.7 seconds at 512 nodes,
both for nested-array, against 8.2 seconds for three transactions. Outside a
reduction no case took more than 13.2 seconds. Sixteen cases therefore use
about 155 of the 900 seconds, and a full sixteen-attempt reduction took 116
seconds more. At 512 nodes, generating sixteen eight-transaction cases wrote at
most 2.4 MB, and the largest cases' reports were at most 4.6 MB, within the 4
MiB native output and 64 MiB artifact limits. A 32-candidate shrink response
for the largest long-bytes and nested-array cases reached 4.13 and 3.35 MB, so
both profiles now cap a response at sixteen candidates, as mapping and ledger
do. The suite's sixteen shrink attempts already capped every batch at sixteen.
The timing runs matched every scenario except one O2 compiler crash at 512
nodes (`stateful-dynamic-array`, recorded in the local questions file). The
three-transaction case from the same seed has the identical source, so the
sequence length is not involved. The crash's reduction removed seven
transactions first.

With scripts and native tools frozen on `c92375a7f`, the thirteen fixed
corpora still pass on O0 and O2 with 167 scenarios and 460 prefixes per level.
Every profile records revision one and no requested length. A random suite of
sixteen eight-transaction cases per profile at the 512-node budget (seed
20261028) passed on both levels with 208 scenarios and 1,664 matched prefixes
per level and no finding. The slowest profile, nested-array, took 153 seconds
on O0 and 143 on O2 of its 900, and no case took more than 11.2 seconds.

**G0 revision three for stateful steps.** Random stateful campaigns now
generate the checked step with
[G0 revision three](../../scripts/SEMANTIC_DIFFERENTIAL.md#revision-three-swarm-masks)
(`core-g0-v3/lcg64-v1`), as the pure profiles do. The definitions:

- Mask: a stateful case's swarm mask is `caseMask` of its scenario seed, the
  seed its step generator receives, and it restricts every helper of the step.
  Transactions, wrappers and protocols do not depend on it.
- Record and replay: a revision-three case records the mask in
  `provenance.swarmMask` (feature names in catalog order), as the pure
  profiles do. Replay requires the mask for revision three, compares a
  generated case's mask with its seed's, and rejects a mask under any other
  revision. Every case tool command replays first, so none of them accepts a
  revision-three case without its mask.
- Reduction: candidates copy their parent's revision and mask.
- Campaigns: the stateful campaigns admit revisions one to three and generate
  random steps with revision three; fixed corpora and saved cases keep the
  version they record, so the fixed corpora stay on revision one, bit for bit.

With scripts and native tools frozen on `6a16989b4`, the thirteen fixed
corpora still pass on O0 and O2 with 167 scenarios and 460 prefixes per level,
all on revision one without a mask. A random suite sample of four
eight-transaction cases per profile (seed 20261029) passed on both levels
with 52 scenarios and 416 prefixes. Every case recorded revision three and
its seed's mask, the slowest profile took 9.1 seconds per case, and there
was no finding. The one excluded seed, in dynamic-array, left too few nodes
for its step template.

**Malformed calldata.** Every other profile sends canonical calldata only. The
`stateful-malformed-calldata` profile sends malformed calldata to the
dynamic-array contract and compares the three paths against the pinned std's
dispatcher and decoder. The definitions were fixed before execution:

- Contract: the dynamic-array step, emitted source and Hull runner are
  reused, so the compiled contract is the dynamic-array one. Its original
  Core contract is a new wrapper, `core-malformed-calldata-contract-v1`. The
  wrapper first evaluates std's checks for `run(uint256,uint256[])` on the
  actual calldata, in std's order, through Core's input host functions:
  `inputDataSize`, `inputDataByte?`, and `inputDataWordBE?`, which yields a
  Word only when all 32 bytes exist. It then runs the dynamic-array protocol
  on the decoded flags, length and elements. The existing profiles, wrappers
  and corpora do not change.
- Reference semantics, from `dispatch.sol` and `std.sol` (`RunContract`,
  `do_exec`, `CalldataWordReader`, `checkArrayHead`, `abiArrayGet`):
  1. Calldata shorter than 4 bytes, or a selector other than `0x9a94c44b`,
     reaches the default fallback, which reverts with `0x4924aef0`.
  2. Calldata shorter than 68 bytes reverts with `0x08638556`
     (`ABIInputTruncated`).
  3. With head offset `o` at byte 36, the call also reverts with
     `0x08638556` when any of these holds:
     - `o > size - 4`;
     - fewer than 32 bytes remain at `4 + o`;
     - the length exceeds `2^251 - 1`, which is `~0 / 32`;
     - `32 * length > size - (36 + o)`.
  4. Otherwise the body runs. Flags are the Word at 4, the length the Word at
     `4 + o`, and element `i` the Word at `36 + o + 32i`. Overlaps are not
     checked and trailing bytes are ignored.
  A std rejection reverts with exactly its four selector bytes and commits
  nothing. Two std errors cannot arise here: `0x7f52b2bf`, because the body
  guards every index by the length, and `0xb5988ea3`, because no transaction
  carries value.
- Malformations, at most 1 KiB of calldata in all:
  - none (the canonical encoding);
  - short calldata: 0 to 3 selector bytes;
  - a wrong selector: xor `1`, `2^31` or `2^32 - 1`;
  - truncation inside the head or inside the tail;
  - trailing bytes: 1, 31, 32, 33 or 64 bytes of `0x00`, `0xff` or a ramp;
  - a head offset:
    - out of range: size − 3, size − 35 and 2^255;
    - wrapping near 2^256: 2^256 − 4, 2^256 − 2 and 2^256 − 1, for which
      `4 + o` wraps to 0, 2 and 3;
    - overlapping the head: 0 and 32;
  - a length:
    - one too long;
    - 2^251, and 2^251 + 1, whose 32-fold product wraps to 32;
    - 2^256 − 1;
    - one shorter, and zero.
  A transaction records its malformation, the resulting calldata, and its
  prescribed std outcome: the rejecting selector, or acceptance. The case
  module computes that prescription with a second std model written directly
  over the calldata bytes. Generation and replay require original Core to
  agree with it.
- Selector rule. When original Core reverts with exactly one of std's error
  selectors as a Word, and the transaction's prescribed outcome is that
  rejection, Rust EVM and imported Hull must each revert with exactly those
  four bytes. The row's Core output is then compared as that selector.
  Everything else is compared exactly: every return, every other revert, and
  every row whose prescription is acceptance, including a body revert whose
  32-byte result happens to equal a selector. Hull against EVM stays byte
  for byte in every row. Each analysis lists the rows compared by selector,
  with their selectors.
  A false agreement remains possible in theory: the Core wrapper's std branch
  and the prescription would both have to reject a transaction that std
  accepts, while both compiled paths also reject it with the same selector.
  Golden cases guard against that.
- Golden cases, before any random run: one per malformation kind, with the
  outcome and selector expected from the reading above. They cover short
  calldata, a wrong selector, a truncated head and tail, trailing bytes,
  out-of-range and wrapping offsets, over-long and wrapping lengths, overlap
  and a shorter length. The decode order is checked too: a wrong selector
  on short or truncated calldata, and truncation beside a bad offset or
  length.
- Observations: as for dynamic-array — status, output, slots 0 to 4 and the
  whole committed storage — compared per prefix. A rejection must keep the
  prior slots and whole storage on every path.
- Generation: the dynamic-array canonical `(flags, values)` blocks. Each
  transaction draws its malformation from the bank above, from a separate
  high-bit stream. Generation validates every prescribed outcome against
  original Core.
- Reduction:
  - one-transaction removals come first, then step reductions;
  - then, for each transaction: replacing its malformation with none, then
    simpler parameters of the same kind;
  - then the dynamic-array element and flags reductions.
  The order counts transactions, then program size, then a malformation
  weight, then elements and values.
- Exclusions:
  - gas;
  - value-bearing transactions, with the non-payable fallback's `0xb5988ea3`
    ordering;
  - calldata over 1 KiB;
  - malformed constructor calldata.
  Every length is checked against the calldata size before any loop or copy,
  so a huge length reverts instead of running out of gas.

What std does with each malformation, from that reading:
- Short calldata and a wrong selector revert with `0x4924aef0`.
- A truncated head, a truncated tail, every out-of-range or wrapping offset, a
  length one too long, `2^251`, `2^251 + 1` and the maximum revert with
  `0x08638556`.
- Trailing bytes are ignored.
- Offset 0 decodes the flags word as the length and runs.
- Offset 32 makes the offset word its own length of 32 and reverts.
- A shorter or zero length decodes a prefix and runs.

Before any random run, the golden cases passed on both models. Once the
compiled contract ran, the Hull and EVM paths of every fixed and random
rejection reverted with exactly the selector the reading predicts.

With scripts and native tools frozen on `20ba7418c`:
- Fixed corpora on O0 and O2: the thirteen existing ones still pass with 167
  scenarios and 460 prefixes per level. The new one matched its 13 scenarios
  and 36 prefixes with complete coverage, 22 of its rows compared by
  selector.
- Random suites of sixteen eight-transaction cases (seed 20261030) at 448 and
  512 nodes matched 16 scenarios and 128 prefixes on each level, every case
  on revision three:
  - at 448 nodes, 81 rows were compared by selector (31 `0x4924aef0`, 50
    `0x08638556`) and 47 transactions were accepted;
  - at 512 nodes, 82 rows were compared by selector and 46 accepted.
- A case took about 7 seconds, so sixteen cases used under two minutes of the
  900-second budget. Four seeds at 448 nodes left too few nodes for their
  step template. There was no finding.

**Malformed nested arrays.** The `stateful-malformed-nested-array` profile
sends malformed calldata to the nested-array contract. It keeps the selector
rule, its narrowing and the `selectorRows` of the malformed-calldata profile.
The definitions were fixed before execution:

- Contract: the nested-array step, emitted source and Hull runner are
  reused, so the compiled contract is the nested-array one
  (`run(uint256,uint256[][])`, `0x7095aff8`). Its original Core contract is
  a new wrapper, `core-malformed-nested-array-contract-v1`. The wrapper
  evaluates std's dispatch and outer decode checks through the same input
  host functions, then runs the nested-array protocol. Each row the body
  reads is checked by std's row decode at the point where the body reads it.
- Reference semantics, from `dispatch.sol` and `std.sol` (the lazy calldata
  array decode, `abiArrayGet`, `checkArrayHead`, `checkReaderRange`):
  1. Dispatch and the outer array are checked as for malformed calldata, with
     this selector. With head offset `o` and outer length `n`, the call
     reverts with `0x08638556` when `32n > size - (36 + o)`, so the offset
     table at `T = 36 + o` is checked whole, including entries for rows the
     body never reads.
  2. The body reads `values.length()`, then, for each row `i < min(n, 3)` in
     order, `values[i]`. That decodes row `i`: with `r` the table word at
     `T + 32i`, it reverts with `0x08638556` when any of these holds:
     - `r > size - T`;
     - fewer than 32 bytes remain at `T + r`;
     - the row length `m`, the Word at `T + r`, exceeds `2^251 - 1`;
     - `32m > size - (T + r + 32)`.
     Element `j` of the row is the Word at `T + r + 32 + 32j`. The body reads
     `j < min(m, 2)` and counts `m`.
  3. Row checks are lazy. A row the body never reads, at index 3 and above,
     is never checked. Row `i` is checked after the rows before it have been
     folded and written; a revert commits nothing, so only the selector is
     observable. A read row's element region is checked whole, including the
     elements the body skips.
  4. Overlaps are not checked. A table entry may point into the table, at
     another row or into a row's elements, and rows may share data. Trailing
     bytes are ignored.
  A std rejection reverts with exactly its four selector bytes and commits
  nothing. `0x7f52b2bf` cannot arise, because the body guards every row index
  by the outer length and every element index by the row length.
  `0xb5988ea3` cannot arise, because no transaction carries value.
- Canonical values have up to four rows of up to three elements. The body
  still reads at most three rows of two elements, so a fourth row and third
  elements exist that it never reads.
- Malformations, one per transaction and at most 1 KiB of calldata:
  - the malformed-calldata kinds on the outer array (none, short calldata, a
    wrong selector, truncation, trailing bytes, a head offset and an outer
    length) with the same banks. Truncation may also cut the offset table or
    a row;
  - a row offset, replacing table entry `k`:
    - out of range: `size - T - 31`, `size - T`, `size - T + 1`, `2^255`;
    - wrapping onto the outer head: `2^256 - 32`, which lands on the outer
      length Word, and `2^256 - 1`;
    - overlapping the table: `0`;
    - overlapping another row: that row's offset, or that offset plus 32;
  - a row length, replacing row `k`'s length Word: one too long, the most
    that fits, one more than fits, `2^251`, `2^251 + 1` (whose 32-fold
    product wraps to 32), `2^256 - 1`, one shorter, and zero.
  Each transaction records its malformation, its calldata and std's
  prescribed outcome. A second std model, written over the bytes, computes the
  prescription, and generation and replay require original Core to agree with
  it.
- Golden cases come before any random run. They cover every kind, and the
  lazy checks:
  - a malformed fourth row and a cut inside it are accepted;
  - a cut inside the offset table is rejected;
  - a cut inside a read row's skipped third element is rejected;
  - a malformed second row is rejected after the first row is folded.
  They also check the decode order: dispatch before decoding, the outer array
  before rows, and an earlier row before a later one.
- Observations: as for nested-array — status, output, slots 0 to 8 and the
  whole committed storage — compared per prefix. A rejection keeps the prior
  slots and whole storage on every path.
- Generation: own canonical blocks of zero to four rows of zero to three
  elements, drawn from the boundary bank, with the nested-array parity
  patterns. Each transaction draws a malformation kind, a parameter and a row
  from a separate high-bit stream.
- Reduction:
  - one-transaction removals first, then step reductions;
  - then, per transaction: no malformation, then simpler parameters of the
    same kind;
  - then the nested-array row, element and flags reductions.
- Exclusions: gas, value-bearing transactions, calldata over 1 KiB, malformed
  constructor calldata, and memory.

What std does with each nested malformation, from that reading:
- Short calldata and a wrong selector revert with `0x4924aef0`.
- These revert with `0x08638556`:
  - a cut in the head, the outer length Word, the offset table or a read
    row, including inside a read row's skipped third element;
  - every bad head offset, including 32;
  - an outer length of `2^251`, `2^251 + 1` or the maximum;
  - an outer length one too long whose extra table entry, the next Word,
    starts a read row.
  For a read row, these also revert:
  - a table Word past the end or at the end;
  - a table Word with a partial length Word, with the high bit, or wrapping
    onto the outer length Word;
  - a table Word into the table other than its own entry;
  - a row length one more than fits, `2^251`, `2^251 + 1` or the maximum.
- These are accepted:
  - trailing bytes;
  - offset 0, which makes the flags the outer length and the offset Word
    the first table Word;
  - a shorter or zero outer length, or one too long whose extra row is the
    fourth;
  - a row on its own table Word, which is then empty;
  - a row that aliases another, or starts inside another row's elements where
    that element fits as a length;
  - a row length up to the most that fits, and a shorter or zero row length;
  - every malformation of, or cut inside, the fourth row, which is never
    decoded.

Before any random run, the golden cases passed on both models. With scripts
and native tools frozen on `bc2932d19`:
- Fixed corpora on O0 and O2: the fourteen existing ones still pass with 180
  scenarios and 496 prefixes per level. The new one matched its 13 scenarios
  and 36 prefixes with complete coverage:
  - its 20 std rejections (8 `0x4924aef0`, 12 `0x08638556`) reverted on Hull
    and EVM with exactly the selector std prescribes;
  - its 16 accepted transactions matched exactly.
- Random suites of sixteen eight-transaction cases (seed 20261031) at 448 and
  512 nodes matched 16 scenarios and 128 prefixes on each level, every case
  on revision three with its mask:
  - the two budgets draw the same transactions, and the step differs in 15
    of the 16 cases;
  - 67 rows were compared by selector (28 `0x4924aef0`, 39 `0x08638556`);
  - 61 transactions were accepted, 15 of them with a row malformation;
  - no seed was excluded.
- A case took about 8.5 seconds. There was no finding.

**Malformed bytes.** The `stateful-malformed-bytes` profile sends malformed
calldata to the long-bytes contract, with the same selector rule, narrowing
and `selectorRows`. The definitions were fixed before execution:

- Contract: the long-bytes step, emitted source and Hull runner are reused, so
  the compiled contract is the long-bytes one (`run(uint256,bytes)`,
  `0x220eb9b6`, a `memory<bytes>` parameter). Its original Core contract is a
  new wrapper, `core-malformed-bytes-contract-v1`: std's dispatch and head
  checks through the same input host functions, std's payload check, then the
  long-bytes protocol on the decoded payload.
- Reference semantics, from `dispatch.sol` and `std.sol` (`decodeBytesLike`,
  `CalldataWordReader`, `checkReaderRange`):
  1. Dispatch and the head are checked as for malformed calldata, with this
     selector: with tail offset `o`, `o > size - 4` or fewer than 32 bytes at
     `4 + o` reverts with `0x08638556`.
  2. With payload length `L`, the Word at `4 + o`, the call reverts with
     `0x08638556` when `L > size - (36 + o)`. std's later
     `require(length <= ~0 - 63)` can then no longer fail, so a length above
     `~0 - 63` is rejected by the first check, with the same selector.
  3. std copies the length Word and the `L` payload bytes into memory and
     zeroes the padding there. The calldata padding is neither required nor
     read: a cut inside it is accepted and nonzero padding is ignored.
  4. The body reads only memory, so it adds no std check. It folds chunk
     `k < 8` when `L > 32k`, stores the last payload byte and the running
     length, and returns or reverts with the slots' sum plus the actual
     calldata size.
  A std rejection reverts with exactly its four selector bytes and commits
  nothing. `0xb5988ea3` cannot arise, because no transaction carries value,
  and the body never indexes the payload.
- In Core, chunk `k` is the aligned calldata Word at `36 + o + 32k` masked to
  the payload. When a cut in the padding leaves that Word incomplete, chunk `k`
  is instead the Word that ends at the last payload byte, which always exists
  once std's check has passed, shifted left to the chunk's start.
- Malformations, one per transaction and at most 1 KiB of calldata: the
  malformed-calldata kinds and banks (none, short, selector, truncate,
  trailing, offset, length), and padding.
  - Truncation cuts inside the head, the length Word, the last payload byte,
    the padding, the last Word or the last byte.
  - Lengths are one too long (inside the padding when there is padding), the
    most that fits, one more than fits, `2^256 - 63` (above `~0 - 63`),
    `2^256 - 1`, `2^255`, one shorter, and zero.
  - Padding is `0xff`, a ramp, or a single `0x01` in the last padding byte; it
    needs a payload that does not fill its last Word.
  Each transaction records its malformation, its calldata and std's
  prescribed outcome, from a second std model written over the bytes.
- Golden cases come before any random run. They cover every kind and std's
  padding rules: a cut inside the padding and nonzero padding are accepted, a
  cut inside the payload is rejected, and a length may run into the padding.
  They also check the decode order. An accepted case must behave exactly like
  the canonical long-bytes contract on the decoded payload, except that its
  result counts the actual calldata size.
- Observations: as for long bytes — status, output, slots 0 to 10 and the
  whole committed storage — compared per prefix.
- Generation: the long-bytes canonical blocks, each transaction drawing a
  malformation kind and parameter from a separate high-bit stream. A kind
  whose bank is empty for the payload, such as padding for a whole number of
  Words, sends the canonical calldata.
- Reduction:
  - one-transaction removals first, then step reductions;
  - then, per transaction: no malformation, then simpler parameters of the
    same kind;
  - then shorter bank payloads, a zeroed payload and the flags reductions.
- Exclusions: gas, value-bearing transactions, calldata over 1 KiB, malformed
  constructor calldata, and memory.

What std does with each bytes malformation, from that reading:
- Short calldata and a wrong selector revert with `0x4924aef0`.
- These revert with `0x08638556`:
  - a cut in the head, the length Word or the payload;
  - every out-of-range or wrapping offset;
  - a length past the data, above `~0 - 63`, `2^255` or the maximum.
- These are accepted:
  - trailing bytes, whose result counts the larger calldata size;
  - a cut inside the padding only;
  - nonzero padding, which is ignored;
  - a length that runs into the padding, up to the most that fits, and a
    shorter or zero length;
  - offset 0, whose payload is the first two bytes of the offset Word;
  - offset 32, whose payload is the original length Word.

Before any random run, the golden cases passed on both models. With scripts
and native tools frozen on `0276e84a9`:
- Fixed corpora on O0 and O2: the fifteen other stateful ones still pass with
  193 scenarios and 532 prefixes per level. The new one matched its 13
  scenarios and 36 prefixes with complete coverage:
  - its 14 std rejections (5 `0x4924aef0`, 9 `0x08638556`) reverted on Hull
    and EVM with exactly the selector std prescribes;
  - its 22 accepted transactions matched exactly.
- Random suites of sixteen eight-transaction cases (seed 20261031) at 448 and
  512 nodes matched 16 scenarios and 128 prefixes on each level, every case
  on revision three with its mask:
  - the two budgets draw the same transactions, and the step differs in 14
    of the 16 cases;
  - 75 rows were compared by selector (30 `0x4924aef0`, 45 `0x08638556`);
  - 53 transactions were accepted, among them seven with nonzero padding,
    seven offset overlaps and a cut inside the padding;
  - all twelve bank payload lengths were sent and no seed was excluded.
- A case took about 6.5 seconds. There was no finding.

**Several methods.** Every other stateful contract has exactly one method,
`run(...)`, so std's dispatcher compares one selector and every transaction
runs the same body. The `stateful-methods` profile gives one contract two to
four external methods over shared storage. The definitions were fixed before
execution.

What std and the compiler do with several methods, from `dispatch.sol`,
`hir-ty/src/prepare.rs` and `hir-ty/src/contract/dispatch.rs`:
1. The compiler collects the contract's public functions in declaration
   order and builds std's method tuple in that order.
2. `RunDispatch` compares the calldata selector, `shr(224, calldataload(0))`,
   with each method's selector in that order and runs the first that matches.
3. Calldata shorter than 4 bytes, or with no matching selector, reaches the
   default non-payable fallback, which reverts with `0x4924aef0` and commits
   nothing.
4. The matched method's `do_exec` requires `calldatasize >= 4 + headSize`,
   else it reverts with `0x08638556`. It then decodes the arguments, runs the
   method, encodes its result and returns.
5. A duplicate public signature (`SC0230`) or a selector collision is a
   compile error.

A probe compiled a three-method contract (arities one, zero and two) over
shared slots at O0 and O2. Imported Hull and the EVM agreed on every call,
including an odd-input revert, a missing selector (`0x4924aef0`), a method
called without its arguments (`0x08638556`) and one called with an extra
Word. The method parity gate already imports the multi-method upstream
fixtures. Original Core reads calldata through its host functions and can
dispatch itself, and the declared-slot Hull runner takes each call's calldata
as given. So neither the shared runtime nor its proofs change.

- Contract: `SynthesizedMethods` declares methods `0..n-1`, with `n` from 2
  to 4 drawn per scenario. For method `i`:
  - its name is `m_` and eight hex digits drawn from the scenario seed;
  - it has `k` uint256 parameters, `k` from 0 to 2;
  - it returns one uint256;
  - its signature is `name(uint256,...)`, and its selector is the first four
    bytes of the signature's Keccak-256.

  Names are distinct. A scenario whose selectors collide is excluded, as the
  compiler would reject it. Each case records the names, signatures,
  selectors and arities.
- Shared storage, the declared slots 0 to 5: slot 0 is a shared accumulator,
  slot 1 a shared call count, and slot `2 + i` method `i`'s last result.
- Method `i` has its own checked aggregate step. Its input is the wrapping sum
  of its arguments, or 0 without arguments. It does the following:
  - sets slot 0 to `step_i(input + slot 0)`;
  - adds one to slot 1;
  - writes the new accumulator to slot `2 + i`;
  - takes the sum of slots 0, 1 and `2 + i` as its result.

  An odd input reverts with that Word; otherwise the method returns it.
  The steps share the step budget equally. Each method's step comes from the
  first of eight seeds of its own stream whose step fits its share, under the
  case's one swarm mask.
- Original Core, `core-methods-contract-v1`:
  - it binds the steps and reads the size;
  - calldata shorter than 4 bytes reverts with `0x4924aef0`;
  - otherwise it compares the selector Word with each method's selector in
    declaration order, through `StdDispatch`;
  - no match reverts with `0x4924aef0`;
  - the match checks its head size (`0x08638556`), reads its arguments and
    runs its protocol.
- Transactions: each transaction either calls one recorded method by name
  with recorded inputs in canonical calldata, or sends a recorded missing
  selector with one Word. The missing selector is that of one more drawn
  name, distinct from every method's. std rejects it with `0x4924aef0`, which
  the existing selector rule and `selectorRows` compare. All transactions are
  zero-value.
- Selector order: the method selectors, read in declaration order, are
  ascending, descending or mixed. Only three or more methods can be mixed.
  Each case records its order.
- Golden dispatch cases come before any random run. They use contracts of two,
  three and four methods whose selectors are ascending, descending or mixed,
  with steps that add a known constant. They call each method, a missing
  selector, short calldata and a method without its arguments, and one
  sequence checks that the methods share storage. Expectations are written
  out by hand.
- Observations: status, output, slots 0 to 5 and the whole committed storage,
  compared per prefix. A rejection keeps the prior slots and whole storage.
- Generation: the method count, names and arities, and the missing selector,
  come from one stream of the scenario seed. Each transaction draws a target
  from another stream: a method, or about one time in `2n + 1` the missing
  selector. Inputs come from the boundary bank.
- Reduction:
  - one-transaction removals come first;
  - then the removal of each method that no remaining transaction calls;
  - then step reductions, method by method;
  - then simpler inputs.

  The order counts transactions, then methods, then program size, then
  inputs.
- Exclusions: gas, value-bearing and payable methods, fallbacks, overloaded
  names, calldata that is neither canonical nor a missing selector, and return
  values other than one Word.

Before any random run, the golden dispatch cases passed on both models. The
first frozen matrices, on `8afe68715`, all matched. Their coverage counts
showed that the generator bounded each target choice to nine values before
reducing it mod `2n + 1`. With two or three methods the missing selector came
one time in nine, and with three the third method was called two thirds as
often as the others. `1e4786c79` draws the choice below `2n + 1`, as defined.
With scripts and native tools frozen on `1e4786c79`:
- Fixed corpora on O0 and O2: the sixteen other stateful ones still pass with
  206 scenarios and 568 prefixes per level. The new one matched its 12
  scenarios and 33 prefixes with complete coverage:
  - three contracts of two methods, five of three and four of four, four in
    each selector order, with calls at every method position;
  - its 5 missing-selector transactions reverted on Hull and EVM with exactly
    `0x4924aef0`;
  - its 28 method calls, 11 of them reverting on an odd input, matched
    exactly.
- Random suites of sixteen eight-transaction cases (seed 20261031) at 448 and
  512 nodes matched 16 scenarios and 128 prefixes on each level, every case
  on revision three with its mask:
  - two contracts of two methods, seven of three and seven of four, twelve of
    them with mixed selectors;
  - the two budgets draw the same contracts and transactions, and a step
    differs in all 16 cases, 47 of the 53 method steps;
  - 19 rows were compared by selector, and 109 method calls were accepted,
    43 of them reverting on an odd input;
  - no seed was excluded.
- A case took about seven seconds. There was no finding.

**Storage-writing loops.** Every other stateful step is straight-line code
over storage. No case runs `sload` or `sstore` inside a loop, where store
forwarding, loop-invariant motion and O2's memory and storage passes act. The
`stateful-storage-loops` profile runs a bounded source `while` loop whose
iterations read and write declared slots. The definitions were fixed before
execution.

A probe preceded them. One hand-written contract ran `input & 7` iterations of
the loop defined below, and a variant omitted the read of slot 1. The results:
- The pinned compiler accepted the loop with its locals declared before it or
  inside it.
- Original Core expressed the loop as seven finite ordinal guards in one host
  contract. It passed the full checker and ran in the unchanged contract
  runtime.
- Over eight transactions (0, 1, 3, 5 and 7 iterations, two reverts after loop
  writes, full-width inputs), imported Hull with O0 and O2 images and the EVM
  on O0, O2 and Yul all matched it. Status, output and slots 0 to 8 agreed,
  and no stray slot was written.
- Yul compiled to one creation/runtime pair whose runtime reads no code.

So neither the shared runtime, the Hull importer nor any proof changes.

- **Contract:** `SynthesizedStorageLoops` with
  `run(uint256 flags, uint256 input)`, selector `0x7357f5d2`. It returns one
  uint256, and every transaction is zero-value.
- **Declared slots 0 to 8:**
  - slot 0, an accumulator;
  - slot 1, the committed iteration total;
  - slots 2 to 8, one per iteration.
- **Loop:** `limit = input & M`, with the plan's mask `M` in {0, 1, 3, 7}. A
  counter `i` runs from 0 while `limit > i`. Iteration `i`:
  - reads slot 0, which the previous iteration wrote;
  - reads slot 1, which the loop never writes;
  - reads slot `1 + i`, which iteration `i - 1` wrote (slot 1 when `i = 0`);
  - reads slot `2 + i`, which the same iteration of an earlier committed
    transaction wrote;
  - writes `step(slot 0 + slot 1 + slot (1 + i) + slot (2 + i) + input)` to
    slot `2 + i` and then to slot 0. The sums wrap.

  After the loop, slot 1 increases by `limit`, and the result is slot 0 plus
  slot 1. Odd flags revert with the result Word after all writes; even flags
  return it.
- **Source** (`solcore-source-storage-loops-v1`):
  - the step is `sc_step`, rendered by the aggregate renderer;
  - the counter, slot and value locals are declared before the loop and
    assigned inside it;
  - slots are computed from the counter (`sc_counter + 2` and `sc_slot - 1`);
  - the loop is a real `while`.
- **Original Core** (`core-storage-loop-contract-v1`, entry `wordOutcomeV1`):
  - it reads the flags and the input and binds `limit = input & M`;
  - `M` ordinal guards follow; guard `i` runs iteration `i` with literal slots
    exactly when `limit > i`;
  - there is no counter cell; the guards are the only loop.
- **Node budget:**
  - the 57-node shell lies inside the budget: the step binding, the input
    reads, the limit, the slot 1 update, the result and the completion;
  - each guard, 45 nodes, lies outside it, at most 315 in all;
  - the suite's default of 384 nodes leaves 327 for the step, whatever the
    mask;
  - contracts are bounded by 512 + 315 nodes.
- **Step:** one checked aggregate step with one to three helpers, generated
  as for the other storage-family profiles. The step must not give equal
  outputs at all boundary inputs.
- **Transactions:** `{id, flags, input, iterations, calldata, value}`, one to
  eight per scenario, drawn in blocks of three from a separate stream. Each
  block draws:
  - three flags from the boundary bank, each with the parity of one of the
    four completion patterns;
  - three input high parts from the bank, with their low three bits cleared;
  - three draws `t` from 0 to 7, which become those low bits.

  A transaction runs `t & M` iterations. The case records that count as
  `iterations`, and replay recomputes it.
- **Mask:** generation draws `M` from {1, 3, 7} by a SplitMix64 hash of the
  seed; plans also admit 0. The plan records `M`.
- **Observations:** status, output, slots 0 to 8 and the whole committed
  storage, per prefix. A revert keeps the prior slots. The adapter checks each
  returned row against the protocol:
  - slot 1 increases by the iteration count;
  - slot 0 equals the last iteration's slot, or is unchanged without
    iterations;
  - the slots above the last iteration are unchanged;
  - the output is slot 0 plus slot 1.
- **Exclusions, in order:**
  - a node budget too small for the shell or above 512;
  - the step's own exclusions;
  - a step whose boundary outputs agree;
  - Core fuel exhaustion (resource);
  - a history that does not follow its prescribed parities.
- **Reductions,** each sealed and strictly smaller in transactions, then
  mask, then program size, then transaction values:
  - one-transaction removals;
  - a lower mask (7, 3, 1, 0), which removes whole guards; the transactions'
    iteration counts follow it;
  - step reductions;
  - simpler transactions: flags to their parity bit, then an input's high
    bits cleared, keeping its iteration count.
- **Fixed corpus coverage:**
  - masks 0, 1, 3 and 7;
  - iteration counts 0 to 7, so zero, one and the maximum;
  - a transaction of at least two iterations, so an iteration reads what the
    previous one wrote;
  - each slot 2 to 8 read by a later transaction after an earlier committed
    one wrote it;
  - both outcomes, including reverts after loop writes;
  - one to three helpers and one to three transactions, with the step
    features, templates and completion patterns of its steps.
- **Golden cases** come before any random run. Steps add a constant, and the
  expectations are written out by hand: 0, 1 and 7 iterations, reverts after
  writes, and carries within and across transactions. A Lean model of the
  source loop, a counter over a slot map, must equal the guarded Core on
  generated cases.
- **Out of scope:** gas, value, other methods, malformed calldata, loop
  bounds other than `input & M`, `for` loops, and `break` or `continue`.

**Results.** The checks before any random run:
- The golden cases passed on both the guarded contract and the source-loop
  model; a flipped expectation fails.
- The model equalled the guarded contract on 392 transactions of 64 generated
  scenarios, and every case and reduction replayed.
- The gate passed on the final tree before `c1f6bde28`: the full Lean build
  and tests, the kernel check, 733 Python tests, every corpus check and the
  diff check.

The matrices ran on `c1f6bde28` with 90 digests frozen: scripts, the 27 native
tools, solc, Anvil, and the Rust driver and code-image exporter. None changed
during any run.
- **Fixed corpora:**
  - O0: all eighteen stateful corpora matched, 230 scenarios and 632
    prefixes; the seventeen earlier ones kept 218 and 601.
  - The new corpus matched its 12 scenarios and 31 prefixes with complete
    coverage on O0, O2 and Yul, in 64, 64 and 101 seconds:
    - masks 0, 1, 3 and 7, and iteration counts 0 to 7;
    - six reverts after loop writes;
    - slots 2 to 8 carried across transactions.
- **Random suites:** root seed `20261028`, sixteen eight-transaction
  scenarios with G0 revision three, at 384 and 512 nodes on O0, O2 and Yul.
  Every run matched 16 scenarios and 128 prefixes:
  - masks 1, 3 and 7 drawn 4, 8 and 4 times;
  - iteration counts 0 to 7 drawn 37, 35, 21, 23, 4, 2, 3 and 3 times;
  - 23 reverts after loop writes;
  - slots 2 to 7 carried across transactions;
  - 16 attempts and no exclusion;
  - the two budgets draw the same masks and transactions, and the step
    differs in 15 of the 16 cases.

A random run took 92 to 98 seconds on Sonatina and 142 to 148 on Yul. There
was no finding. Hosted CI has not run the profile.

**Loops over Keccak-addressed entries and logs.** `stateful-storage-loops`
uses a literal slot per iteration. The recorded O2 crashes are in the log,
forwarded-value and dynamic-array profiles, where memory, Keccak and log
lowering meet. No generated case yet hashes a slot or emits a log inside a
loop. The `stateful-keccak-loops` profile does both in every iteration. The
definitions were fixed before execution.

A probe preceded them. One hand-written contract ran the loop defined below
with the step `x * 3 + 1` and the key masks 0, 1 and 7, over eight
transactions. Those had 0, 1, 2, 3, 5, 6 and 7 iterations, reverts after
three and five logged iterations, and entries reused within and across
transactions. The results:
- The pinned compiler accepted the std mapping and the `log2` wrapper inside a
  source `while` loop.
- Original Core expressed the loop as seven finite ordinal guards in one host
  contract, with the mapping profile's Core Keccak closure and the event-log
  profile's log framing. It passed the full checker and ran in the unchanged
  contract runtime; seven iterations needed 500,000 to 700,000 fuel.
- Imported Hull with O0 and O2 images and the EVM on O0, O2 and Yul all
  matched it on status, output, the whole committed storage and every log's
  topics and data, with no stray slot.
- Yul compiled to one creation/runtime pair whose runtime reads no code.

So neither the shared runtime, the Hull importer nor any proof changes. The
dynamic-array profile's array is calldata and its slots are literals, so the
Keccak-addressed construct here is the std mapping, as in `stateful-mapping`.
One profile carries both constructs: they share one loop, and every iteration
needs both.

- **Contract:** `SynthesizedKeccakLoops` with
  `run(uint256 flags, uint256 input)`, selector `0x7357f5d2`. It returns one
  uint256, and every transaction is zero-value.
- **Fields:** `acc: word` at slot 0 and `entries: mapping(word => word)` at
  base slot 1. The entry of `key` lies at `keccak256(1 ++ key)`, std's layout
  as in the mapping profile.
- **Plan:** a step, a loop mask `M` and a key mask `S`, each in
  {0, 1, 3, 7}.
- **Loop:** `limit = input & M` and `base = input & ~7`. A counter `i` runs
  from 0 while `limit > i`. Iteration `i`:
  - uses the key `base | (i & S)`;
  - reads its entry and `acc`;
  - writes `step(entry + acc + input)` to the entry and then to `acc`, with
    wrapping sums;
  - emits `log2` with one data Word, the written value, and the topics `i`
    and the key.

  After the loop the result is `acc + limit`. Odd flags revert with the
  result after all writes and logs; even flags return it.
- **Entries:** iterations `i` and `j` address the same entry when
  `i & S = j & S`. So `S = 0` gives every iteration one entry, `S = 1`
  alternates two, `S = 3` cycles four and `S = 7` gives each iteration its own.
  Transactions whose inputs share the high part share entries.
- **Source** (`solcore-source-keccak-loops-v1`):
  - the counter, key and value locals are declared before the loop;
  - std's `entries[sc_key]` does the hashing;
  - a 64-byte log buffer is reserved from the free-memory pointer before the
    loop, as the event-log profile does;
  - the log is `sc_log2(sc_ptr, 32, sc_counter, sc_key)`.
- **Original Core** (`core-keccak-loop-contract-v1`, entry `wordOutcomeV1`):
  - it binds the mapping profile's Keccak closure, the step, the flags, the
    input and the limit;
  - `M` ordinal guards follow. Guard `i` runs exactly when `limit > i`: it
    builds the key with the literal `i & S`, hashes it through the closure,
    reads and writes, and emits one framed log;
  - each log is framed as the event-log profile frames logs: a header for two
    topics and one data Word, the data record, then the two topic records,
    through `emitLogWord`;
  - there is no counter cell.
- **Node budget:**
  - the 38-node shell lies inside the budget;
  - the 2,654-node Keccak closure and the 69-node guards lie outside it, the
    guards at most 483 in all;
  - the suite's default of 384 nodes leaves 346 for the step;
  - contracts are bounded by 512 + 2,654 + 483 nodes.
- **Fuel:** the default direct fuel of 1,000,000 per transaction applies. A
  history that runs out is excluded as a resource.
- **Step:** one checked aggregate step with one to three helpers, as for the
  other storage-family profiles. Its boundary outputs must not all agree.
- **Transactions:** `{id, flags, input, iterations, calldata, value}`, one to
  eight, drawn in blocks of three exactly as in `stateful-storage-loops`.
  `iterations` is `input & M`; it is recorded, checked on decode and
  recomputed on replay.
- **Masks:** generation draws `M` from {1, 3, 7} and `S` from {0, 1, 3, 7},
  each by its own SplitMix64 hash of the seed.
- **Observed slots:** slot 0 and the entry slot of every key that the
  scenario's transactions address, in increasing numeric order. They are
  derived with the independent `Solcore.Abi.V1.Keccak256`, as the mapping
  profile does. Whole storage is compared, and Hull and the EVM must hold no
  nonzero undeclared slot.
- **Logs:** each transaction's ordered committed logs are compared on all
  paths, as in the event-log profile, together with the EVM chain's complete
  log list. A revert commits none, and the deployment emits none.
- **Protocol check** of each returned row:
  - it has one log per iteration, and log `i` has the topics `i` and its key
    and one data Word;
  - slot 0 equals the last log's data, or is unchanged without iterations;
  - each addressed entry holds the data of the last log with its key, and
    every other observed slot is unchanged;
  - the output is slot 0 plus the iteration count.
- **Exclusions, in order:**
  - a node budget too small for the shell or above 512;
  - the step's own exclusions;
  - a step whose boundary outputs agree;
  - Core fuel exhaustion (resource);
  - a history that does not follow its prescribed parities.
- **Reductions,** each sealed and strictly smaller in transactions, then
  loop mask, then key mask, then program size, then transaction values:
  - one-transaction removals;
  - a lower loop mask (7, 3, 1, 0), which removes whole guards;
  - a lower key mask (7, 3, 1, 0), which merges entries;
  - step reductions;
  - flags to their parity bit, then an input's high bits cleared, keeping
    its iteration count.
- **Fixed corpus coverage:**
  - loop masks 0, 1, 3 and 7, key masks 0, 1, 3 and 7, and iteration counts
    0 to 7, so zero, one and the maximum;
  - the carry `iteration`: an iteration reads the `acc` the previous one
    wrote;
  - the carry `entry`: an iteration reads an entry an earlier iteration of
    its transaction wrote, so two iterations address the same entry;
  - the carry `transaction`: a transaction reads an entry an earlier committed
    transaction wrote;
  - the carry `rollback`: a revert after logged iterations;
  - the six boundary Words as inputs;
  - one to three helpers and transactions, with the step features, templates
    and completion patterns of its steps.
- **Golden cases** come before any random run. Steps add a constant, and the
  expectations are written out by hand:
  - slot 0, the entries and every log, for key masks 0, 1 and 7;
  - zero, one and seven iterations;
  - a revert after logged iterations;
  - entries reused within and across transactions.

  A Lean model of the source loop must equal the guarded Core on generated
  cases. The model is a counter over a slot map with Keccak slots from
  `Solcore.Abi.V1.Keccak256` and a log list.
- **Out of scope:** gas, value, other methods, malformed calldata, keys
  other than `base | (i & S)`, logs other than one `log2` per iteration,
  `for` loops, and `break` or `continue`.

**Results.** The checks before any random run:
- The golden cases passed on both the guarded contract and the source-loop
  model; a flipped log value, entry or status fails.
- The model equalled the guarded contract on 240 transactions of 40 generated
  scenarios, on status, output, the observed slots and every log. Every case
  and the reductions of four cases replayed.
- The gate passed on the final tree before `46335fa59`: the full Lean build
  and tests, the kernel check, 752 Python tests, every corpus check and the
  diff check.

The matrices ran on `46335fa59` with 91 digests frozen: scripts, the 28 native
tools, solc, Anvil, and the Rust driver and code-image exporter. None changed
during any run.
- **Fixed corpora:**
  - O0: all nineteen stateful corpora matched, 243 scenarios and 665
    prefixes; the eighteen earlier ones kept 230 and 632.
  - The new corpus matched its 13 scenarios and 33 prefixes with complete
    coverage on O0, O2 and Yul, in 103, 111 and 137 seconds:
    - loop masks and key masks 0, 1, 3 and 7, and iteration counts 0 to 7;
    - 77 committed logs and six reverts after logged iterations;
    - all four carries.
- **Random suites:** root seed `20261029`, sixteen eight-transaction
  scenarios with G0 revision three, at 384 and 512 nodes on O0, O2 and Yul.
  Every run matched 16 scenarios and 128 prefixes:
  - loop masks 1, 3 and 7 drawn 5, 3 and 8 times, and key masks 0, 1, 3 and 7
    drawn 3, 3, 6 and 4 times;
  - iteration counts 0 to 7 drawn 33, 33, 20, 11, 12, 6, 6 and 7 times;
  - 191 committed logs and 26 reverts after logged iterations;
  - by case: an iteration reading the previous one's `acc` in 11, a repeated
    entry within a transaction in 7, an entry carried across committed
    transactions in 15 and a rollback after logs in 13;
  - 16 attempts and no exclusion;
  - the two budgets draw the same masks and transactions, and the step
    differs in 14 of the 16 cases.

A random run took 128 to 178 seconds on Sonatina and 221 to 222 on Yul. There
was no finding. Hosted CI has not run the profile.

Further state/ABI work, such as deeper nesting, static multi-word ABI elements
(`uint256[3]` or tuples), `bytes` beyond 256 bytes, strings, ABI-encoded
return values, which first need a contract entry convention for more than one
Word, or callers beyond the three fixed senders, needs its own observation,
rollback, deployment and reduction definitions first.
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
and rollback with revert bytes. The public theorems now carry the
init-template catalog and the premise that connects it to the compiled init
definitions and runtime images, with every existing consumer passing the empty
catalog; the Hull design document lists exactly how each statement changed and
the remaining proof obligations, starting with an evaluation lemma for the
actual image comparison.

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
