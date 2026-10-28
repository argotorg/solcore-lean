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
| 1 | CI and continuous bounded random campaigns across all existing profiles | Local gate complete; continuous fuzzing driver implemented; automatic CI triggers disabled, manual dispatch only; no passing hosted run yet; the pinned end-to-end fixture comparison runs only locally | Reproducible CI jobs, scheduled seed exploration, retained findings and verified cancellation/resource limits. |
| 2 | Generated Sonatina O2, then Yul comparisons | Local gate complete; the twenty-four storage-family profiles also run on Yul when selected and are validated locally; the two call profiles stay on Sonatina; the pinned end-to-end fixtures run on Hull, O0, O2 and Yul in a standalone comparison of the compiled paths, without an original Core reference, with a recorded O2 compiler crash | The same original cases run on each enabled backend with explicit backend provenance and replay. |
| 3 | Missing runtime operation mappings | Implemented; O2 random run has a recorded finding | Tested Rust-dialect mappings, dynamic-input regressions, generation, reduction and replay for each added operation. |
| 4 | Richer generated grammar | Call-graph, loop and aggregate families validated locally; G0 generator revision four, revision three's per-case swarm masks restricted to each emitter's features, is the random default for the seventeen G0-based pure profiles; random runtime-input campaigns add four seeded inputs to each function's boundary inputs, can request whole functions and, in the fifteen profiles whose functions can be identities, exclude functions that return every boundary input unchanged, generating whole functions in as many case-tool requests as the 2 MiB response limit needs; nested bounded loop, bounded recursion, inline Yul, loop-closure, recursive-loop, inline Yul loop, inline Yul memory, user-defined enum, trait and trait hierarchy profiles are validated locally on O0, O2 and Yul; pure campaigns compile each distinct source once per backend; an O2 random comptime run, the O0 and Yul random inline Yul runs, the O0, O2 and Yul random inline Yul loop runs and the O2 random inline Yul memory run have recorded compiler crashes, the fixed and random Yul trait runs and the fixed Yul trait hierarchy run a recorded solc rejection, and the random trait hierarchy runs a recorded frontend rejection on every backend; hosted run pending | Broader typed compositions with bounded generation and reductions that preserve binding, effects and failure identity. |
| 5 | A minimal proof for the actual Rust-dialect emitter | Closed, runtime-input, named-helper, raw-primitive, call-graph, private-mutation, aggregate, aggregate call-graph, call-graph loop, aggregate loop, generic, two-slot storage, two-slot rollback, keyed-storage and event-log emitters proved locally; other emitters open | A small connected meaning-preservation theorem for what is actually emitted, not for a substitute native Lean syntax. |
| 6 | State and ABI extensions | Keyed-storage, bounded dynamic-array, event-log, call-value, bounded-`bytes`, contract-forwarded value, Keccak-addressed mapping, sender-keyed ledger, 256-byte `bytes`, nested `uint256[][]`, malformed-calldata, several-methods, storage-loop, Keccak-loop, tuple-return, inline Yul storage-loop and Keccak-loop, bounded `bytes`-return, enum and struct storage, enum-return and enum-argument extensions validated locally, malformed calldata for the dynamic-array, nested-array and 256-byte `bytes` contracts and comparing std error reverts by selector, two to four external methods on one contract dispatched as std does, a bounded source loop whose iterations read and write declared slots, a bounded source loop whose iterations read and write Keccak-addressed mapping entries and emit one log each, static ABI tuple returns of two to four Words through the `wordTupleOutcomeV1` contract entry convention, both loop plans with every storage access, entry hash and log in inline Yul blocks around the Solcore step call, `bytes` returns of up to 64 bytes through the `boundedBytesOutcomeV1` convention, user-defined enum and struct values in contract fields and behind mapping keys through `std.StorageGeneric`, returned user-defined enums of two to four constructors through the `enumOutcomeV1` convention, and user-defined enum arguments decoded by std's derived decoder, canonical and malformed, compared by std's selector or empty revert data; all twenty-six stateful profiles compare the observed contracts' whole committed storage on all three paths; random stateful campaigns generate steps with G0 revision three and sequences of up to eight transactions; `bytes` returns beyond 64 bytes, returned enums and enum arguments beyond the recorded shapes and other dynamic return values are not built; O2 random log, forwarded-value and dynamic-array runs have recorded compiler crashes; hosted run pending | Explicit additional observations and transaction semantics, with actual three-way tests and sequence reduction. |
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
output and no unresolved libraries or immutable references. The twenty-four
storage-family profiles are admitted under the stateful Yul boundary below,
which names the first fifteen; `stateful-storage-loops`,
`stateful-keccak-loops`, `stateful-tuple-returns`,
`stateful-assembly-storage-loops`, `stateful-assembly-keccak-loops`,
`stateful-bytes-returns`, `stateful-adt-storage`, `stateful-enum-returns` and
`stateful-enum-arguments` joined later under the same boundary.
`export-rust-yul.py --fixture` separately admits a pinned end-to-end fixture's
own contract under the same checks, for a comparison of the compiled paths
that has no original Core. The two call
profiles, other code-observing programs and arbitrary nested objects remain
excluded until their layout and observation boundary are connected explicitly.
This scope does not require bytecode-layout or gas equality between the three
paths.

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

**Inline Yul memory.** No generated case stored to or loaded from memory
inside an `assembly` block, although the recorded O2 crashes cluster where
memory, Keccak and log lowering meet, and the inline Yul path found a crash
that Solcore's own lowering never reached. The Yul front end lowers `mload`,
`mstore`, `mstore8` and `keccak256` with their own byte placement, apart from
the memory that Solcore's lowering allocates. One new pure profile,
`runtime-assembly-memory`, renders a step's arithmetic through memory in one
`assembly` block. The step's argument and results pass through Words stored
and loaded at aligned, unaligned and overlapping offsets above the
free-memory pointer, together with byte writes and an optional `keccak256`
over a written range.

Before any code, a probe compiled ten sources with the pinned compiler and std
and ran them on every path: checked Hull export, Sonatina O0 and O2 code
images, Yul through `export-rust-yul.py` and the pinned solc, Anvil, and the
Lean Hull runner. Each was one `assembly` block in `run`, apart from the
free-memory source:
- a base from `mload(64)`, `mstore` of Words at aligned and unaligned offsets,
  and `mload` at the same, overlapping and unaligned offsets, each read
  feeding a Yul step function whose result the next write stores;
- `mstore8` at the first, last and interior bytes of a Word and at the last
  byte of the window, read back by overlapping loads;
- overwrites in both width orders: a byte over a Word, a Word over a byte and
  a byte over a byte, then reads of the overwritten bytes;
- `keccak256` over 0, 1, 31, 32, 33 and 64 written bytes, at aligned and
  unaligned offsets, two of them in one block;
- a block that fills 128 bytes above the free-memory pointer with ones without
  moving it, followed by a Solcore helper that allocates from the pointer
  with std's `mload` and `mstore`, a second block that checks the pointer moved
  by the helper's 64 bytes only, and the ordinary return.

All of them matched a byte model of the source at twelve inputs on every path,
and Foundry's `cast keccak` agreed with the model's Keccak-256 on every hashed
length. So writing above the free-memory pointer without moving it is safe
for the surrounding Solcore code here: neither the helper nor the return
encoding depends on the bytes left there. A Lean check built the hash of each
length as a Core closure from the Core Keccak-f[1600] permutation and digest
builders of the Hull import path, the builders of the mapping profile's
closure. Each closure converted to Wire, passed the full checker and agreed with
the separate `Solcore.Abi.V1.Keccak256` on three message pairs. The 64-byte
closure equals the mapping profile's closure. The same check compared the window
model below with a byte-list model on eight schedules and ten inputs, and all
80 agreed. Core, the Hull importer and runner, both EVM backends and
`export-rust-yul.py` need no change, and no shared runtime code or proof
changes. The existing profiles,
corpora, emitters and emitter proofs stay unchanged, and this emitter has no
proof yet. The definitions were fixed before execution:

- Step: the `runtime-primitives` function of the case seed, generated by the
  same steps as for `runtime-assembly` (the G0 program under the same swarm
  mask, then the same literal abstraction), written `f` below.
- Window: the block reads `sc_base := mload(64)` once and uses the 96 bytes
  from it without moving the free-memory pointer. It first writes the
  prologue: `x`, `f(x)` and `not(x)` at offsets 0, 32 and 64, for the input
  `x`. No read then depends on memory the block did not write, which
  Solcore's code and the two backends leave differently.
- Schedule, drawn from the case seed by a SplitMix64 stream with its own domain
  (`0x61736d6d656d6f01`):
  - one to three stages; stage `i` reads `sc_m<i> := mload(add(sc_base, r))`
    at a word offset and writes `sc_step(sc_m<i>)` with `mstore` at a word
    offset or with `mstore8` at a byte offset;
  - a final read `sc_m<n>` at a word offset;
  - no hash, or `sc_h := keccak256(add(sc_base, h), L)` for `L` in 0, 1, 31,
    32, 33 and 64, with `h + L ≤ 96`;
  - the block sets `sc_out := sc_step(sc_m<n>)`, or
    `add(sc_step(sc_m<n>), sc_h)` with a hash, and `run` returns it.

  Word offsets lie in 0..64 and byte offsets in 0..95, so every access stays
  inside the window.
- Deltas: an offset's delta is its position modulo 32, the byte at which it
  starts within a prologue Word. The delta classes are 0, 1, 2–15, 16, 17–30
  and 31. Generation draws an offset's class uniformly, then its delta in the
  class, then its Word: 0, 32 or 64 for delta 0 and 0 or 32 otherwise for a
  word access; 0, 32 or 64 for a byte write.
- Draws, in this order, one stream value each: the stage count; per stage the
  read offset (class, delta, Word), the width and the write offset; the final
  read offset; the hash, none or one of the six lengths with equal weight;
  then its offset in 0..96 − `L`.
- Yul rendering: the step is the Yul function `sc_step(sc_arg) -> sc_ret` at
  the top of the block, its body in the `switch` form of `runtime-assembly`.
  An offset renders as `add(sc_base, o)`, and as `sc_base` for zero. The wrapper
  is `run(uint256)` of `SynthesizedAssemblyMemory`.
- Core reference (`core-assembly-memory-v1`), with no memory: the window is
  three let-bound Words, starting `x`, `f(x)` and `not(x)`, and Words past it
  are zero.
  - A read at `32k + d` is `w_k` for `d = 0`, and otherwise
    `(w_k << 8d) | (w_{k+1} >> 8(32 - d))`.
  - A word write of `v` at `32k + d` rebinds `w_k` to `v` for `d = 0`, and
    otherwise binds `w_k := (w_k & high(d)) | (v >> 8d)` and
    `w_{k+1} := (w_{k+1} & low(32 - d)) | (v << 8(32 - d))`, where `high(d)`
    keeps the first `d` bytes of a Word and `low(n)` its last `n`.
  - A byte write of `v` at `32k + d` binds
    `w_k := (w_k & ~(0xff << 8(31 - d))) | ((v & 0xff) << 8(31 - d))`.
  - `f` is the primitive function's checked Core lambda, let-bound once and
    applied to `x` and to each read Word.
  - The hash is a let-bound Core closure applied to the Words read at `h` and,
    for `L` above 32, at `h + 32`. It absorbs the first `L` bytes of the pair
    with Ethereum's `0x01` domain byte and final `0x80` as one Keccak block,
    then applies the Core Keccak-f[1600] permutation and digest builders of the
    Hull import path, which are proved against `KeccakSemantics`. At `L = 64`
    the closure is the mapping profile's closure.

  The reference never translates the Yul text. A registered test compares it
  with a byte-list model of the schedule that hashes with the separate
  `Solcore.Abi.V1.Keccak256`, and each length's closure with `cast keccak`.
- Bounds: the step's budget is that of `runtime-assembly`: default 96 nodes,
  its minimum, and at most 512, and the applied step is checked against it.
  The schedule's Core (at most 116 nodes) and the closure (2,270 nodes at
  `L = 0` to 2,654 at `L = 64`) lie outside it, so the complete program is
  checked against a case limit of 3,282 nodes. A hash costs about 81,000 Core
  fuel, inside the default fuel of 1,000,000.
- Inputs: the primitive profile's eight boundary inputs; random campaigns add
  the four seeded inputs.
- Exclusions, under the stage `assembly-memory-profile`: the step's generation
  exclusions, as for `runtime-assembly`; then, on the composed program at the
  eight boundary inputs, a result other than a Word, fuel exhaustion (an
  inconclusive resource exclusion), or the same Word for all eight.
- Identity filter: without a hash the composed function can return its input,
  as an identity step reading the untouched first Word does, so random
  campaigns apply `exclude-boundary-identity-v1` as for `runtime-assembly`.
- Reductions, in order:
  - remove one stage, keeping at least one;
  - remove the hash, or shorten it to a shorter admitted length at the same
    offset;
  - align one offset, setting its delta to zero in the same Word;
  - then the primitive reductions of the step: G0 shrinking under the
    abstraction, then the inputs 0, 1 and half the input, with the schedule
    unchanged.

  Every candidate is sealed by the full checker and strictly smaller,
  lexicographically, in stage count, hash rank, delta sum, then the step's
  nodes and literal weight. A reduced origin records the parent plan and
  input. A shrink response holds at most eight candidates of a plan with a
  hash: each embeds the closure, so the response stays below the campaign's
  2 MiB tool-output limit.
- Specified memory shapes, from the plan, never measured:
  - stages: the stage count;
  - accesses: `read:<class>` for stage and final reads, `word:<class>` and
    `byte:<class>` for writes;
  - hazards: `waw:<earlier>-<later>` when a stage write overwrites a byte that
    an earlier stage wrote and a later read or the hash reads that byte before
    it is written again; `raw:same` for a read at a stage word write's offset
    whose 32 bytes all come from that write; `raw:overlap` for a read with
    bytes from a stage word write at another offset; `raw:byte` for a read
    with a byte from a stage byte write; `raw:hash` for a hashed range with a
    byte from a stage write;
  - hashes: `none` or the length.
- Fixed corpus coverage: stage counts 1, 2 and 3; all eighteen accesses, so
  both widths and every delta class; `waw:word-word`, `waw:word-byte`,
  `waw:byte-word`, `raw:same`, `raw:overlap`, `raw:byte` and `raw:hash`;
  `none` and every hashed length; and the eight boundary inputs.
  `waw:byte-byte` needs two byte writes at one byte and is generated but not
  required. The corpus is generated with the default budget: from seed 1
  upwards, every seed whose plan is accepted, passes the shift rule below and
  covers a missing value is taken, until nothing is missing, each function at
  all eight inputs.
- The fixed corpus skips plans that may compile to a shift by a constant
  count of at least 2^64, the construct of the recorded crash, by the folding
  rule of `runtime-assembly-loops` extended through memory. A read may fold
  when every byte it reads was last written by a value that may fold: `x` and
  `not(x)` never may, and `f(m)` may when the step's result may fold for that
  argument. An application of the step to a read that may fold must not make
  one of its shift counts fold. Random campaigns still generate such plans,
  and any new crash goes only to the local questions file.

The profile was implemented at `1d2ea9cef` with the definitions above:
- `Solcore.Synthesis.Core.AssemblyMemory` (the window model and the Keccak
  closures), `AssemblyMemoryEmitter` and `AssemblyMemoryCases`, the case-tool
  commands `assembly-memory-generate` and `assembly-memory-emit`, and campaign
  and suite registration. The profile joins the revision-four, acceptance and
  emitter-support registries as `runtime-assembly` did, with the boundary
  identity of seed 108.
- A registered Lean test checks:
  - each length's closure against `cast keccak` and
    `Solcore.Abi.V1.Keccak256`, and the 64-byte closure against the mapping
    profile's closure;
  - a fixture's source against a golden text and its Core results against
    golden values from a separate Python byte model;
  - the reference against a byte-list model on 192 generated cases.

  Generation draws every stage count, width, delta class and hash option and
  replays exactly. Tampering is refused, and reductions are strictly smaller
  and replay.
- A fixed corpus of 80 cases from ten seeds between 1 and 52, covering every
  stage count, access, required hazard and hash option. Of the first 52
  seeds, 15 were excluded and five skipped by the shift rule.

Frozen matrices at `1d2ea9cef` (the freeze digest did not change):
- The fixed corpus matched all 80 cases on O0, O2 and Yul with complete stage,
  access, hazard, hash and input coverage, compiling 10 sources, in 142, 138
  and 236 seconds, under load averages of 15 to 85 from other work on the
  machine.
- Random suites from root seed 1 with eight whole functions took 9 attempts,
  excluding one plan whose eight boundary outputs agreed. They drew 96 cases
  from 8 sources: all three stage counts, 14 of the 18 accesses, hashes of 32,
  33 and 64 bytes and none, and the hazards `waw:word-word`, `waw:word-byte`,
  `raw:overlap`, `raw:byte` and `raw:hash`. Each hashed case embeds its
  closure, so the first generation responses exceeded the 2 MiB limit. The
  campaign's chunked generation retried three times, then requested one
  function at a time.
- O0 and Yul matched all 96 cases, in 150 and 203 seconds. On O2, 84 matched
  and the twelve inputs of the sixth function crashed code-image export with
  `Integer overflow when casting to usize`, in 293 seconds. Its reduction
  kept the fingerprint with one aligned stage, no hash and a step that shifts
  by `signextend` of two literals, which O0 and Yul compiled. The crash is
  retained as a finding and recorded locally without investigation, so the
  O2 random gate did not pass.

**User-defined enums and match.** Every generated program so far uses Words,
std pairs and std sums. User-defined `enum` declarations, `match` over them
and their constructor layout are untouched, although the pinned checkout's
own end-to-end fixtures place its recent defects there: match substitution in
a specialized trait impl, pattern binding order, scopes of folded matches and
repeated pattern bindings. Only original Core can catch a front-end defect
that every backend shares, so one new pure profile, `runtime-enums`, keeps an
independent Core reference: an enum as nested Core sums and products and a
`match` as nested `caseE`. Traits with generic impls are left to a later unit.

Before any code, a probe compiled eight hand-written sources with the pinned
compiler and std and ran them on every path: checked Hull export, Sonatina O0
and O2 code images, Yul through `export-rust-yul.py` and the pinned solc,
Anvil, and the Lean Hull runner, at twelve inputs against a Python model of
each source. Together they covered:
- plain enums of two to four constructors with zero to two fields, and fields
  of Word, tuple, enum and generic-instance type;
- generic enums of one and two parameters at Word, tuple and enum arguments,
  including a generic enum whose field is another generic enum at its own
  parameter, and a generic function over a generic enum at two instances;
- values built from the runtime input by constructor choices on its low bits;
- nested constructor and tuple patterns, `_` in fields, components and
  columns, `default`, `case _` and `case (_)`, a variable catch-all, matches of
  two and three columns, and nested matches on bound enum and tuple values;
- pattern variables that shadow a parameter, an enclosing arm's variable and
  each other across arms;
- the leading-dot constructor form in patterns and returned values, and a
  constructor named like its enum, unqualified;
- traits with impls at Word, at tuples and std sums under constraints
  (`impl<f, g> T<sum<f, g>> where f: T, g: T`), at a plain enum and at a
  generic enum, unary and binary methods with nested matches on both
  arguments, and a generic function constrained by the trait.

All 24 runs matched on every path. The compiler rejects other unqualified
constructors (`SC0106`), so the profile writes constructors qualified, in the
dot form or by a same-name constructor. A non-exhaustive match is an error and
an unreachable arm a warning, so generated matches are exhaustive with every
arm reachable. Twelve plans of the generator below, emitted and run on O0, O2
and Yul, matched their Core reference in all 36 runs, on the EVM and in the
Hull runner. Core, the Hull importer and runner, both EVM backends and
`export-rust-yul.py` need no change, and no shared runtime code or proof
changes. The existing profiles, corpora, emitters and emitter proofs stay
unchanged, and this emitter has no proof yet. The definitions were fixed
before execution:

- Declarations (`core-enum-match-v1`), one to three, `Sc_T0` to `Sc_T2` at the
  top level. Each is plain or generic in one parameter `a`, with two to four
  constructors of zero to two fields. A field is a Word, `a` (generic only), a
  tuple of two components (Word, `a` or an earlier enum), or an earlier enum,
  a generic one at Word, `(word, word)` or `a`. Constructor `k` of `Sc_Ti` is
  `Sc_Ti_k`; with the same-name option, constructor 0, which has a field, is
  `Sc_Ti`. No declaration refers to itself or a later one.
- Views, one to three, each one function with one `match` over its
  scrutinees and a Word parameter `sc_w`:
  - `single`: one value of an enum or of a generic enum's instance;
  - `pair`: two such values, matched as two columns;
  - `generic`: a generic function over `Sc_Ti<a>`, called at two distinct
    instances; its patterns bind but never inspect values of type `a`.
- Arms: two to six random rows of patterns, each kept only if useful after
  the earlier rows; then, at random, a row for every remaining first-column
  constructor with variable or wildcard fields; then, if the rows are not
  exhaustive, a catch-all: `default`, wildcards, or a variable first. At most
  eight arms. A pattern is a constructor pattern (qualified, dot or
  same-name), a tuple pattern, a variable (`sc_a` to `sc_d`, or `sc_w`, which
  shadows the parameter) or `_`, refined with probability 3/4, 1/2 and 1/3 at
  the first three levels, so nesting is at most three. Names within a row are
  distinct and repeat freely across arms.
- Bodies: `return` of a left fold of up to four terms, every Word the row
  binds and then possibly one more term (a visible Word or a constant), by
  drawn `+`, `-`, `^` and `*`, plus a 64-bit arm constant. A quarter of the
  arms that bind an enum or tuple value instead match it again: two to four
  arms drawn the same way, at most six, whose variables may rebind the
  enclosing arm's names. A name means its innermost binding: the nested arm,
  the enclosing arm, then `sc_w`.
- Builders: per scrutinee, or per instance of a generic view, a function
  `sc_make<v>_<b>(sc_x: word)` returning one to four values, the value
  selected by the residue `(sc_x + offset) & 3` for an offset in 0..3, the last
  value for every residue past it. A value is a constructor tree whose Word
  leaves are `sc_x`, `(sc_x + c)`, `(sc_x ^ c)` or `(sc_x * c)`. Each value is
  the first of four random candidates whose first matching arm no earlier
  value selects, by first top-level constructor for a pair view. A returned
  value may use the dot form; nested constructors are qualified or same-name.
- `run(uint256)` of `SynthesizedEnums` calls each view on its builders' values
  of `input` and on `input + w`, a per-view constant, and returns
  `r_0 + 3 r_1 + 5 r_2 + …` over the calls, a generic view counting twice.
- Draws come from the case seed by a SplitMix64 stream with its own domain
  (`0x656e756d6d617401`), in plan order: the declarations, the view count,
  then for each view its kind, Word constant, scrutinee types and instances,
  arms, bodies and builders. Constants are small, 64-bit, high-bit or near
  the maximum.
- Core reference, with no source text and no data definitions:
  - a Word is a Word, a tuple a product, and an enum the right-nested sum of
    its constructors' payloads (Unit, the field, or the product of two
    fields), substituted at its instance;
  - a value is its chain of `inLeft` and `inRight` over its payload;
  - a builder is a closure from Words; a view is a closure per instance over
    its scrutinees and the Word;
  - a match is compiled arm by arm: each arm but the last runs with the
    let-bound thunk of the remaining arms as its failure, a constructor
    pattern unwraps the sum chain with nested `caseE`, a tuple or two-field
    payload pattern projects and let-binds the components it tests, and a
    variable names the matched value; the last arm is reached only when
    exhaustiveness says it matches;
  - the entry binds every call's Word in order and combines them.

  Admission checks pattern types, distinct names, scoping, usefulness of
  every arm and exhaustiveness of every match by the pattern-matrix algorithm,
  computed here without the compiler. A registered Lean test compares the
  reference with a direct interpreter of the plan's first-match semantics.
- Bounds: every closed type's Core type has at most 64 type nodes, a
  declaration whose widest instance would exceed that keeps Word fields only,
  and a case's complete reference is limited to 4,096 nodes. The node budget,
  default 2,048, minimum 256 and at most 4,096, bounds the applied reference:
  views are dropped from the end while it is exceeded and more than one
  remains. Of the first 500 seeds, the median reference had 327 nodes and the
  largest 1,799.
- Inputs: the primitive profile's eight boundary inputs; random campaigns add
  the four seeded inputs.
- Exclusions, under the stage `enum-profile`: a single view over the budget;
  then, at the eight boundary inputs, a result other than a Word, fuel
  exhaustion (an inconclusive resource exclusion), or the same Word for all
  eight, as for 20 of the first 500 seeds.
- Identity filter: an arm can return a leaf whose constant cancels its own,
  so random campaigns apply `exclude-boundary-identity-v1`.
- Reductions, each followed by pruning arms that became unreachable, turning
  terms whose name no longer means a Word into 0 and nested matches on an
  unbound name into their first inner body:
  - remove a view, keeping one;
  - remove a constructor from a declaration of three or more: arms naming it
    are removed, a value using it becomes the first remaining constructor with
    `sc_x` leaves, later constructors are renumbered, and removing a same-name
    constructor drops the option;
  - remove a field of a constructor, with its subpatterns and values;
  - flatten a field to a Word: subpatterns there become `_` and values `sc_x`;
  - remove an arm, or end a match at an arm with `default` and its body;
  - replace a constructor or tuple subpattern with `_`;
  - replace a nested match by its first inner body;
  - remove a body term, or a builder value, keeping one;
  - replace a leaf by `sc_x`;
  - remove an unused declaration;
  - then the inputs 0, 1 and half the input, with the plan unchanged.

  Every candidate is admitted and sealed by the full checker, and strictly
  smaller lexicographically in plan size (constructors, field-type weights,
  views, arms, pattern nodes, body terms, inner arms and value nodes), then
  input. A reduced origin records the parent plan and input. A shrink response
  stops before its cases would exceed 1.5 MB, below the campaign's 2 MiB
  tool-output limit.
- Specified enum shapes, from the plan, never measured:
  - constructors: each declaration's constructor count;
  - fields: `count:<n>` per constructor and `type:<kind>` per field, a kind
    being `word`, `param`, `tuple`, `enum` or `applied`;
  - declarations: `plain`, `generic`, `same-name`, and `argument:<kind>` for
    each generic instance's argument (`word`, `tuple`, `enum` or `param`);
  - views: the view kinds;
  - patterns: `qualified`, `dot`, `same-name`, `nullary`, `tuple`,
    `variable`, `wildcard`, `default`, `nested`, `shadow` (a variable named
    `sc_w`), `repeated` (a name bound by two arms of one match), `rebound` (a
    nested arm binding a name of its enclosing arm) and `exhaustive` (a match
    with no catch-all row);
  - wildcards: `_` as a constructor `field`, a tuple `component`, a `column`
    of a row that is not a catch-all, a whole `arm`, or `deep` below two
    layers;
  - depths: each pattern's nesting depth, 1 to 3.
- Fixed corpus coverage: every value above and the eight boundary inputs. The
  corpus is generated with the default budget: from seed 1 upwards, every seed
  whose plan is accepted and covers a missing value is taken, until nothing is
  missing, each plan at all eight inputs.

The profile was implemented at `9400b4e08` with the definitions above:
- `Solcore.Synthesis.Core.EnumData` (declarations, closed instances, values,
  builders and the stream, written to be shared with a trait profile),
  `EnumMatch` (patterns, views, the pattern-matrix check, the Core compilation
  and the shapes) and `EnumShrink` (reductions); `EnumEmitter` and `EnumCases`;
  the case-tool commands `enum-generate` and `enum-emit`; and campaign and
  suite registration. The profile is not G0-based; it joins the acceptance
  registry as the thirteenth identity-filter profile, with no identity seed.
  The case tool, the campaign's `maximum_nodes` and the suite's budget cap
  take its budget up to 4,096 nodes; every other profile keeps 512.
- A registered Lean test checks:
  - a fixture's source against a golden text, and its results on the Core
    reference and on a direct interpreter of the plan against golden values
    from a separate Python model;
  - that admission refuses an arm after `default`, an unreachable arm, a
    non-exhaustive match, a constructor out of range, a misplaced same-name
    pattern, a nested dot value, a name bound twice in a row, a body naming a
    non-Word, a nested match on a Word, a generic view inspecting `a`, a
    forward declaration reference and a nullary same-name constructor;
  - the reference against the interpreter on the plans of 240 seeds at twelve
    inputs.

  Generation is deterministic, draws every shape value within 600 seeds and
  replays exactly, also with seeded inputs and the identity filter; constant
  plans are excluded, and a 256-node budget drops views. Tampering is refused,
  and every kind of reduction applies, is strictly smaller and replays.
- A fixed corpus of 56 cases from seven seeds between 1 and 58, covering every
  shape value; of the first 58 seeds, 3 were excluded.

Frozen matrices at `9400b4e08` (the freeze digest did not change):
- The fixed corpus matched all 56 cases on O0, O2 and Yul with complete shape
  and input coverage, compiling 7 sources, in 167, 193 and 207 seconds, under
  load averages of 43 to 70 from other work on the machine.
- Random suites from root seed 1 with eight whole functions took eight
  attempts without an exclusion and drew 96 cases from 8 sources in one
  generation request. They drew all three constructor counts, view kinds and
  depths, every declaration kind and instance argument, every wildcard
  position, every field count and field kind but a plain enum, and every
  pattern form but `default`, `rebound` and the same-name pattern. All 96
  matched on O0, O2 and Yul, in 179, 220 and 325 seconds, so no finding was
  recorded.

**Traits with constrained generic impls.** The enum profile leaves traits
untouched, although the pinned checkout's own fixtures place a recent defect
there: specializing a binary method of `impl<f, g> T<sum<f, g>>` at
`sum<(word, word), word>` leaked a substitution from one alternative of its
match into the other's nested `match`, so `yule` rejected the emitted Hull
(`specialise-sum-of-product`). Only original Core can catch a front-end
defect that every backend shares, so one new pure profile, `runtime-traits`,
calls one trait's methods at instances built from Words, tuples, std sums and
user-defined enums, directly and through constrained generic functions, and
keeps an independent Core reference: one monomorphic closure per instance
type and method the uses reach.

Before any code, a probe compiled a hand-written source with one trait of a
unary and a binary method; impls at `word`, at `(f, g)` and `sum<f, g>` under
constraints, at a plain enum and at two generic enums
(`impl<a> T<E<a>> where a: T`); both binary match forms; constrained generic
helpers that call the trait at their parameter and at `(t, t)`; and values
with `inl` and `inr` inside tuples and constructor fields, at generic enums
applied to a sum, a tuple and a generic enum. It ran with the pinned compiler
and std on every path: checked Hull export, Sonatina O0 and O2 code images,
Yul through `export-rust-yul.py` and the pinned solc, Anvil, and the Lean Hull
runner, at twelve inputs against a Python model. O0 and O2 matched on the EVM
and in the Hull runner. On Yul, solc rejected the exported Yul with a
`StackTooDeepError` in `sc_both` specialized at `sum<word, Sc_T0>`. The test
fixture's emitted source and twelve plans of the generator below, run the
same way, matched their Core reference in 38 of 39 runs. Only the plan of
seed 2 was rejected, on Yul, in the same way, in `sc_both` at
`Sc_T0<(word, sum<word, word>)>`; both rejections are recorded locally without
investigation. The Hull runner needs more than the probe's 10,000,000 fuel to
deploy seed 2's O0 image and matches within the suite's 40,000,000 default. Core, the Hull importer and runner, both EVM backends and
`export-rust-yul.py` need no change, and no shared runtime code or proof
changes. The existing profiles, corpora, emitters and emitter proofs stay
unchanged, and this emitter has no proof yet. The definitions were fixed
before execution:

- Declarations: those of `runtime-enums`, drawn by `EnumData` from this
  profile's stream: one to three `Sc_T0` to `Sc_T2`, plain or generic in `a`,
  with two to four constructors of zero to two fields.
- Trait (`core-trait-instances-v1`): `trait Sc_Fold<a>` with the unary
  `sc_fold(sc_x: a) returns (word)` and the binary
  `sc_both(sc_x: a, sc_y: a) returns (word)`. A generated plan has both; a
  reduced plan may keep one, and every impl then implements only it.
- Impls, in the order Word, tuple, sum, declarations; a generated plan has
  all of them, a reduced one those its uses and its kept impls need:
  - `impl Sc_Fold<word>`: `sc_fold` returns `(sc_x op c)` and `sc_both`
    `((sc_x comb sc_y) op c)`;
  - `impl<f, g> Sc_Fold<(f, g)> where f: Sc_Fold, g: Sc_Fold`: one arm,
    `case (sc_a, sc_b)`, folding the method at both components;
  - `impl<f, g> Sc_Fold<sum<f, g>> where f: Sc_Fold, g: Sc_Fold`: arms
    `inl(sc_a)` and `inr(sc_b)`; `sc_both` always has the regression shape, a
    nested `match (sc_y)` in both arms that recurses on the same side and
    returns a mismatch constant on the other;
  - at each declaration, `impl Sc_Fold<Sc_Ti>`, or
    `impl<a> Sc_Fold<Sc_Ti<a>> where a: Sc_Fold` when generic: one arm per
    constructor in order, binding its fields as `sc_a` and `sc_b` (`sc_c` and
    `sc_d` for `sc_y`), a same-name constructor unqualified.

  An arm folds the method's results at its bound values with a drawn
  operator, then applies a drawn operator with a drawn constant; an arm with
  one operand has no fold and a nullary arm returns its constant. `sc_both` of
  a tuple or a declaration is drawn `nested` (`match (sc_x)`, then
  `match (sc_y)` in each arm) or `columns` (`match (sc_x, sc_y)` with a row per
  constructor); a declaration ends each match of `sc_y`, or the two-column
  match, with `default`, which returns the impl's mismatch constant.
  Operators are `+`, `-`, `^` and `*`; constants are small, 64-bit, high-bit
  or near the maximum, drawn per arm and per impl.
- Helpers, emitted when a use needs them, each with its own drawn operator and
  constant, all `where t: Sc_Fold`: `sc_once<t>` and `sc_twice<t>` call the
  method at their parameter; `sc_lift<t>` and `sc_lift2<t>` call it at
  `(t, t)`, as `Sc_Fold.sc_fold((sc_x, sc_x))` and
  `Sc_Fold.sc_both((sc_x, sc_y), (sc_y, sc_x))`.
- Uses, one to six, each one call: a method; a call form, `direct`,
  `generic` or `lifted`, weighted 2, 1 and 1; a closed instance type; and a
  builder. An instance type is a Word, a tuple or std sum of two instance
  types, a plain declaration, or a generic one at an instance type. Its depth
  (a Word 0, a plain declaration 1, a tuple or sum one more than its deepest
  component, a generic declaration one more than its argument) is drawn from
  0 to 3 with weights 1, 3, 3 and 3, and the type is the first of four
  candidates of that depth whose called type fits the type limit, otherwise a
  Word. A unary use calls the method at its builder's value of `input`; a
  binary use also at its value of `input + s`, with `s` from 1 to 4, so that
  `s = 4` keeps the residue.
- Builders: `sc_u<i>(sc_x: word)` per use, one to four values selected by the
  residue `(sc_x + offset) & 3` as in `runtime-enums`. A value is a tree of
  constructors, `inl`, `inr` and tuples with Word leaves `sc_x`,
  `(sc_x + c)`, `(sc_x ^ c)` or `(sc_x * c)`, the first of four candidates
  whose top constructor or side no earlier value has. A returned value may use
  the dot form; nested constructors are qualified or same-name.
- `run(uint256)` of `SynthesizedTraits` returns `r_0 + 3 r_1 + 5 r_2 + …` over
  the uses.
- Draws come from the case seed by a SplitMix64 stream with its own domain
  (`0x7472616974730001`), in plan order: the declarations, the impls, the four
  helpers, the use count, then each use's method, call form, depth, type
  candidates, shift and builder.
- Core reference, with no source text and no data definitions:
  - Words, tuples and enums as in `runtime-enums`; a std sum is lowered as a
    plain declaration of two one-field constructors after the plan's, so its
    Core type is the binary sum and `inl` and `inr` are `inLeft` and
    `inRight`;
  - one closure per instance type and method reachable from the uses: the
    use's type, or `(t, t)` for a lifted use, and transitively a tuple's or
    sum's components and a declaration's fields at its instance, let-bound
    bottom-up, components first, in the order first reached;
  - each closure compiles its impl's match by `EnumMatch`'s arm-by-arm
    compilation (nested `caseE` over the sum chain, projections and the
    fall-through thunks), and a method call at a bound value applies the
    closure of that value's type;
  - a closure per helper and instance, the builders as closures from Words,
    and the entry, which binds every use's Word in order and combines them.

  Admission checks the declarations as `runtime-enums` does, every impl's
  arms, operators, form and mismatch constants, that impls are distinct and
  ordered and every impl a kept declaration's fields resolve to is present,
  that the helpers are exactly those the uses need, and every use's method,
  type, depth, shift and builder values. A registered Lean test compares the
  reference with a direct interpreter that dispatches each method by the
  instance type when it is called.
- Bounds: every called type's Core type, `(t, t)` included, has at most 64
  type nodes and no fuel exhaustion, and a case's complete reference is
  limited to 4,096 nodes. The node budget, default 2,048, minimum 256 and at
  most 4,096, bounds the applied reference: uses are dropped from the end while
  it is exceeded and more than one remains, with the helpers only they needed.
  Of the first 500 seeds, the median reference had 773 nodes, the largest
  3,531 before and 2,030 after fitting, and 23 plans dropped uses.
- Inputs: the primitive profile's eight boundary inputs; random campaigns add
  the four seeded inputs.
- Exclusions, under the stage `trait-profile`: a single use over the budget;
  then, at the eight boundary inputs, a result other than a Word, fuel
  exhaustion (an inconclusive resource exclusion), or the same Word for all
  eight, as for 22 of the first 500 seeds.
- Identity filter: a single Word use whose arm multiplies by 1 returns its
  input, so random campaigns apply `exclude-boundary-identity-v1`; none of the
  first 500 seeds was an identity.
- Reductions, each followed by recomputing the helpers the uses need, a newly
  needed one adding 0:
  - remove a use, keeping one;
  - remove a method from the trait and every impl when no use calls it;
  - remove an impl that no use and no kept impl needs;
  - reduce nesting: replace one node of a use's type by a Word, a tuple or sum
    by one of its components, or a generic declaration by its argument,
    mapping each builder value to the new type (`sc_x` where a node became a
    Word, the smallest value where no value maps);
  - call a lifted use generically and a generic use directly;
  - remove a builder value, keeping one, or replace a leaf by `sc_x`;
  - remove a declaration nothing refers to, with its impl;
  - then the inputs 0, 1 and half the input, with the plan unchanged.

  Every candidate is admitted and sealed by the full checker, and strictly
  smaller lexicographically in plan size (declarations, methods, impl arms
  and constants, helpers, call forms, type nodes and value weights), then
  input. A reduced origin records the parent plan and input. A shrink
  response stops before its cases would exceed 1.5 MB.
- Specified trait shapes, from the plan, never measured:
  - instances: `<kind>:<method>` for every reachable closure, a kind being
    `word`, `tuple`, `sum`, `plain` or `generic`;
  - calls: `<method>:<call>` for every use;
  - depths: each use type's depth, 0 to 3;
  - arguments: the kind of every reachable generic declaration's argument;
  - forms: `tuple:` or `enum:` and the binary match form of every reachable
    binary tuple or declaration closure;
  - shapes: `sum-of-product`, a reachable binary sum closure whose components
    differ in kind, one of them a tuple, as in the upstream fixture.
- Fixed corpus coverage: every value above and the eight boundary inputs. The
  corpus is generated with the default budget: from seed 1 upwards, every seed
  whose plan is accepted and covers a missing value is taken, until nothing is
  missing, each plan at all eight inputs. It does not avoid the Yul
  `StackTooDeepError`, whose construct is not known without investigation.

Method-level generics, traits of several parameters, superclass constraints,
method values and `comptime` trait arguments, which the fixtures
`trait-method-generics` and `comptime-trait-arguments` exercise, are not
generated.

The profile was implemented at `9fe2cb27f` with the definitions above:
- `Solcore.Synthesis.Core.TraitPlan` (instance types, values, the trait's
  impls, helpers and uses, admission, the lowering of std sums, the reached
  instances, the Core reference, the shapes and generation, reusing
  `EnumData`'s declarations, builders and stream and `EnumMatch`'s compilation
  of `match`) and `TraitShrink` (reductions); `TraitEmitter` and
  `TraitCases`; the case-tool commands `trait-generate` and `trait-emit`; and
  campaign and suite registration. The profile is not G0-based; it joins the
  acceptance registry as the fourteenth identity-filter profile, with no
  identity seed, and takes budgets up to 4,096 nodes as `runtime-enums` does.
- A registered Lean test checks:
  - a fixture's source against a golden text, and its results on the Core
    reference and on a direct interpreter against golden values from a
    separate Python model; the fixture reaches every instance kind under both
    methods, every call form and generic argument kind, both match forms of a
    declaration and the sum-of-product shape;
  - that admission refuses a use without the sum impl, a declaration impl
    without the Word impl, impls out of order, a missing arm, a fold operator
    on a one-operand arm, an operator on a nullary arm, a two-column sum
    match, one sum mismatch constant, an unneeded and a missing helper, a
    binary use without a shift or shifted by five, a shifted unary use, a use
    four levels deep, a generic declaration used as plain, a nested dot value,
    a misplaced same-name value, a use of a method the trait lacks, a lifted
    use over the type limit and seven uses;
  - the reference against the interpreter on the plans of 200 seeds at twelve
    inputs.

  Generation is deterministic, draws every shape value within 300 seeds and
  replays exactly, also with seeded inputs and the identity filter, and a
  256-node budget drops uses. Tampering is refused, and every kind of
  reduction applies, is strictly smaller and replays.
- A fixed corpus of 40 cases from five seeds between 1 and 7, covering every
  shape value; none of the first seven seeds was excluded.
- The campaign now also dispatches an `enumPlan` corpus entry to `enum-emit`
  (`7dcd00fa1`); before, a pinned reduced enum plan failed with no generation
  request or program.

Frozen matrices at `9fe2cb27f` (the freeze digest did not change), under
load averages of 9 to 68 from other work on the machine:
- The fixed corpus matched all 40 cases on O0 and O2 with complete shape and
  input coverage, compiling 5 sources, in 113 and 137 seconds. On Yul, 32
  matched and the eight cases of seed 2 were rejected by solc with a
  `StackTooDeepError` in `sc_both`, in 338 seconds; the matched cases still
  cover every shape value and input.
- Random suites from root seed 1 with eight whole functions took eight
  attempts without an exclusion and drew 96 cases from 8 sources in two
  generation requests, after one output-limit retry. They drew every shape
  value except a plain enum as a generic argument. All 96 matched on O0 and
  O2, in 193 and 206 seconds. On Yul, 84 matched and the twelve cases of the
  third function were rejected in the same way, in 404 seconds.
- Automatic reduction kept the fingerprint with one binary use in each: the
  rejected Yul function is `sc_both` at `Sc_T0<word>` under a two-column
  match, and at `Sc_T0<Sc_T0<(word, word)>>` under a nested one. The
  rejections are recorded locally without investigation, so the Yul fixed
  and random gates did not pass; no mismatch was found.

**Trait hierarchies and method-level generics.** `runtime-traits` calls one
trait. The pinned fixtures `superclass-dictionaries` (a trait bound by
another, chains of two such bounds, a superclass method called through a
subclass bound, method values and generic function values),
`trait-method-generics` (a trait method with its own type parameter, called
at two instances of it, also as a value) and `comptime-trait-arguments` were
each a regression fixture upstream. One new pure profile,
`runtime-trait-hierarchies`, puts a subclass of `runtime-traits`' trait and a
chain above it into that profile's plans, with helpers bounded only by a
subclass, method values, generic function values and the subclass's own
method-level generic, and keeps an independent Core reference. It is a new
profile rather than a second version of `runtime-traits`: it calls
`TraitPlan`'s trait, impls, instance types, values, builders and closures
unchanged, so `runtime-traits`' generator, corpus and matrices stay valid,
while a second version would retire them without making either plan simpler.

Before any code, a probe over unit 13's declarations, trait and impls
compiled hand-written sources with the subclass `Sc_Sub<a> where a: Sc_Fold`
as a marker, with its own method-level generic
`sc_mix<u>(sc_x: a, sc_y: u) returns (word) where u: Sc_Fold`, and with that
method named `sc_fold`, like the superclass's; the chain
`Sc_Top<a> where a: Sc_Sub`; impls of both at Words, tuples, std sums, a plain
and two generic enums; helpers bounded by `Sc_Sub` or `Sc_Top` that call the
superclass's methods directly, as a method value or through a generic
function value of another helper; the subclass's method directly, through
`Sc_Top` and as a method value, each at two argument types; method and
generic function values at closed types; `comptime` trait arguments; and a
method returning its own type parameter. It ran on every path as unit 13's
probe did, against a Python model at twelve inputs:
- At small types every form matched on O0, O2 and Yul, on Anvil and in the
  Lean Hull runner, and so did the values at closed types and the `comptime`
  arguments at larger types. Three sources at larger types matched on O0 and
  O2, and solc rejected their exported Yul with a `StackTooDeepError` in the
  base trait's methods, as in unit 13: `sc_both` at `Sc_T1<sum<word, word>>`
  and at `Sc_T1<Sc_T1<word>>`, and `sc_fold` at a tuple of two
  `(word, sum<word, word>)`.
- The checked frontend rejects a base-trait method reached through two
  superclass steps, `Sc_Top` to `Sc_Sub` to `Sc_Fold`, at a tuple, a std sum
  or a generic declaration, with `SC0401` ("cannot specialize expression:
  type is not concrete") and `SC0406` ("missing evidence: superclass …:
  Sc_Fold: no unique dictionary"): in a `Sc_Top`-bounded helper that calls
  the method, or that calls a `Sc_Sub`-bounded helper directly or as a
  function value. It accepts the same calls at a Word and at a plain
  declaration, and one step at every kind: a `Sc_Sub`-bounded helper, a
  function value inside one, and the subclass's own method through `Sc_Top`.
  This is recorded locally without investigation.
- Twelve plans of the generator below, seeds 1 to 12: eight contain a
  base-method `top` use at such a type and were rejected on every backend;
  the other four matched their Core reference on O0 and O2, and three on
  Yul, the plan of seed 9 being rejected in `sc_both` at
  `Sc_T0<Sc_T0<word>>`.

Core, the Hull importer and runner, both EVM backends and
`export-rust-yul.py` need no change, and no shared runtime code or proof
changes. The existing profiles, corpora, emitters and emitter proofs stay
unchanged, and this emitter has no proof yet. The definitions were fixed
before execution:

- Declarations, the base trait `Sc_Fold` and its impls: `runtime-traits`',
  drawn by `TraitPlan` from this profile's stream; a generated plan has both
  base methods and every base impl, the sum impl's `sc_both` with the
  regression shape.
- Subclass (`core-trait-hierarchies-v1`), one form per plan with equal
  weights: the marker `trait Sc_Sub<a> where a: Sc_Fold {}`; or with its own
  method `sc_mix<u>(sc_x: a, sc_y: u) returns (word) where u: Sc_Fold`; or
  with that method named `sc_fold`, like the superclass's, every call being
  qualified (`Sc_Sub.sc_fold(…)` beside `Sc_Fold.sc_fold(…)`). The chain is
  the marker `trait Sc_Top<a> where a: Sc_Sub {}`.
- Impls of `Sc_Sub` and of `Sc_Top`, in the order Word, tuple, sum,
  declarations, each at a head where its superclass has an impl; a generated
  plan has all of them, a reduced one those its uses and its kept impls need:
  - `impl Sc_Sub<word>`, `impl<f, g> Sc_Sub<(f, g)> where f: Sc_Sub, g: Sc_Sub`,
    `impl<f, g> Sc_Sub<sum<f, g>> where f: Sc_Sub, g: Sc_Sub`, and
    `impl Sc_Sub<Sc_Ti>` or `impl<a> Sc_Sub<Sc_Ti<a>> where a: Sc_Sub`; the
    same for `Sc_Top`, whose impls are empty, as are a marker's;
  - with a method, the Word impl returns
    `((sc_x comb Sc_Fold.sc_fold(sc_y)) op c)`; any other matches `sc_x`, one
    arm per constructor in order binding its fields as `sc_a` and `sc_b`,
    folds `Sc_Sub.sc_mix(v, sc_y)` at the bound values with a drawn operator,
    then applies a drawn operator with a drawn constant; a nullary arm returns
    its constant. Operators and constants are drawn as for the base impls.
- Helpers, emitted when a use needs them, in this order, each returning
  `(… op c)` with its own drawn operator and constant:
  - `sc_up<t>` and `sc_up2<t>` where `t: Sc_Sub`, calling
    `Sc_Fold.sc_fold(sc_x)` and `Sc_Fold.sc_both(sc_x, sc_y)`: one bound;
  - `sc_top<t>` and `sc_top2<t>` where `t: Sc_Top`, calling the same: the
    chain of two bounds;
  - `sc_val<t>` and `sc_val2<t>` where `t: Sc_Sub`, calling a method value,
    `let sc_f = Sc_Fold.sc_fold;` then `sc_f(sc_x)`;
  - `sc_fun<t>` and `sc_fun2<t>` where `t: Sc_Sub`, calling a generic
    function value, `let sc_f = sc_up;` then `sc_f(sc_x)`, with `sc_up` or
    `sc_up2` emitted too;
  - `sc_mixt<t, u>` where `t: Sc_Top, u: Sc_Fold`, calling
    `Sc_Sub.sc_mix(sc_x, sc_y)` through one bound, and `sc_mixv<t, u>` where
    `t: Sc_Sub, u: Sc_Fold`, calling the method value
    `let sc_f = Sc_Sub.sc_mix;`.
- Uses, one to six, each one method, one call form, a closed receiver type
  and a builder:
  - methods `unary` (`sc_fold`), `binary` (`sc_both`) and, when the subclass
    has its method, `mix`, with equal weights;
  - call forms with equal weights: for a base method `direct`, `sub`, `top`,
    `value` or `function`; for `mix`, `direct` (`Sc_Sub.sc_mix`), `top`
    (`sc_mixt`) or `value` (`sc_mixv`);
  - a receiver type drawn as in `runtime-traits`: a depth from 0 to 3 with
    weights 1, 3, 3 and 3, the first of four candidates of that depth whose
    Core type fits the type limit, otherwise a Word;
  - a binary use also calls at the builder's value of `input + s`, `s` from
    1 to 4; a `mix` use calls at two argument types of the method's own
    parameter, drawn in the same way, the second the first candidate that
    differs from the first (otherwise a Word, or `(word, word)` when the first
    is a Word), each with its builder, `sc_v<i>` and `sc_w<i>`, at `input`, and
    its Word is the sum of the two calls.
- Builders as in `runtime-traits`, `sc_u<i>` for receivers. `run(uint256)` of
  `SynthesizedTraitHierarchies` returns `r_0 + 3 r_1 + 5 r_2 + …` over the
  uses.
- Draws come from the case seed by a SplitMix64 stream with its own domain
  (`0x7472616974730002`), in plan order: the declarations, the base impls,
  the subclass form, the steps of its impls, the ten helpers, the use count,
  then each use's method, call form, receiver depth and candidates, shift,
  builder, and for `mix` each argument's depth, candidates and builder.
- Core reference, with no source text and no data definitions:
  - `TraitPlan`'s closures of the base methods, unchanged, for every type and
    method reachable from a unary or binary use's receiver and from the
    argument of every subclass closure at a Word, components first, in the
    order first reached;
  - one closure per receiver and argument type of the subclass's method
    reachable from a `mix` use, the receiver's components at the same
    argument first, compiled by `EnumMatch`'s arm-by-arm compilation; at a
    Word it applies the argument's base fold closure;
  - a closure per helper and instance: its operator and constant over the
    base method's closure at the instance, so a superclass call through a
    subclass bound, of one step or two, is the superclass instance's closure;
    over the `sub` helper's closure for `function`; or over the subclass
    closure at the receiver and argument;
  - the builders as closures from Words, receivers then arguments, and the
    entry, which binds every use's Word in order and combines them.

  Admission checks the declarations and base impls as `runtime-traits` does,
  the subclass form, that the `Sc_Sub` and `Sc_Top` impls are distinct,
  ordered and over an impl of their superclass at the same head, with a method
  one step per constructor and every impl a declaration's fields resolve to
  present, that the helpers are exactly those the uses need, and every use's
  method, call form, types, depths, shift, two distinct argument types,
  builder values and the impls its calls need. A registered Lean test
  compares the reference with a direct interpreter that dispatches each
  method by the instance type when it is called.
- Bounds as in `runtime-traits`: every receiver's and argument's Core type
  has at most 64 type nodes and no fuel exhaustion, a case's complete
  reference at most 4,096 nodes, and the node budget, default 2,048, minimum
  256 and at most 4,096, bounds the applied reference by dropping uses from
  the end. Of the first 500 seeds, the median reference had 1,128 nodes, the
  largest 8,224 before and 2,710 after fitting, 108 plans dropped uses and
  three kept a single use over the budget.
- Inputs: the primitive profile's eight boundary inputs; random campaigns add
  the four seeded inputs.
- Exclusions, under the stage `hierarchy-profile`: a single use over the
  budget; then, at the eight boundary inputs, a result other than a Word,
  fuel exhaustion (an inconclusive resource exclusion), or the same Word for
  all eight, as for 10 of the first 500 seeds.
- Identity filter: as in `runtime-traits`, a single Word use whose arm
  multiplies by 1 returns its input, so random campaigns apply
  `exclude-boundary-identity-v1`; none of the first 500 seeds was an
  identity.
- Plans keep generating a base-method `top` use at every receiver type. 192
  of the first 500 seeds have one at a tuple, std sum or generic declaration,
  which the frontend rejects, so random campaigns report those plans as
  `source-rejected`.
- Reductions, each followed by recomputing the helpers the uses need, a newly
  needed one adding 0:
  - remove a use, keeping one;
  - remove a base method when no use calls it, the unary one only without a
    subclass method;
  - name a shadowing subclass method `sc_mix`, or remove the subclass's
    method when no use calls it;
  - remove an impl of any of the three traits that no use and no kept impl
    needs;
  - reduce the nesting of a receiver or argument type as `runtime-traits`
    does, mapping its builder values;
  - call a `top`, `value` or `function` use through `sub`, or any use
    directly;
  - remove a builder value of a receiver or argument, keeping one, or replace
    a leaf by `sc_x`;
  - remove a declaration nothing refers to, with its impls;
  - then the inputs 0, 1 and half the input, with the plan unchanged.

  Every candidate is admitted and sealed by the full checker, and strictly
  smaller lexicographically in plan size (declarations, base methods, impl
  arms and constants, the subclass form, its impls' steps, the chain's impls,
  helpers, call forms, type nodes and value weights of receivers and
  arguments), then input. A reduced origin records the parent plan and input.
  A shrink response stops before its cases would exceed 1.5 MB.
- Specified hierarchy shapes, from the plan, never measured:
  - instances: `<kind>:<method>` for every reachable base closure and
    `<kind>:mix` for every reachable subclass closure, a kind being `word`,
    `tuple`, `sum`, `plain` or `generic`;
  - calls: `<method>:<call>` for every use;
  - depths: each receiver type's depth, 0 to 3;
  - arguments: the kind of every reachable generic declaration's argument;
  - parameters: the kind of every argument type of the subclass's method;
  - forms: `tuple:` or `enum:` and the binary match form of every reachable
    binary base closure at a tuple or declaration;
  - subclass: `marker`, `mix` or `shadow`.
- Fixed corpus coverage: every value above and the eight boundary inputs. The
  corpus is generated with the default budget: from seed 1 upwards, every
  seed whose plan is accepted and covers a missing value is taken, until
  nothing is missing, each plan at all eight inputs, except a plan with a
  base-method `top` use at a tuple, std sum or generic declaration. It does
  not avoid the Yul `StackTooDeepError`.

`comptime` trait arguments compiled and matched on every path in the probe,
but only with constant values: they would need a constant-only value form and
a `comptime` qualification of every position of a type, and their uses would
not depend on the input, so they do not fit one plan and are not generated. A
method returning its own type parameter also matched and is not generated,
`sc_mix` being this profile's method-level generic. Traits of several
parameters and method values at closed types are not generated either.

The profile was implemented at `68ead60e4` with the definitions above:
- `Solcore.Synthesis.Core.HierarchyPlan` (the subclass form, its impls and the
  chain's, helpers, uses with their arguments, admission, the lowering of
  receivers and arguments, the reached base and subclass closures, the Core
  reference, the shapes and generation, calling `TraitPlan`'s trait, impls,
  instance types, values, builders, closures and draws and `EnumMatch`'s
  compilation of `match` unchanged) and `HierarchyShrink` (reductions);
  `HierarchyEmitter`, which emits the base trait and impls through
  `TraitEmitter`, and `HierarchyCases`; the case-tool commands
  `hierarchy-generate` and `hierarchy-emit`; and campaign and suite
  registration. The profile is not G0-based; it joins the acceptance registry
  as the fifteenth identity-filter profile, with no identity seed, and takes
  budgets up to 4,096 nodes as `runtime-traits` does.
- A registered Lean test checks:
  - a fixture's source against a golden text, and its results on the Core
    reference and on a direct interpreter against golden values from a
    separate Python model; the fixture calls `sc_mix` directly, through
    `Sc_Top` and as a method value at all five argument kinds, a binary
    `top` use at a plain declaration, a generic function value and a method
    value; its shadowing variant has the same results and the same source
    with `sc_mix` renamed `sc_fold`, and its emitted source matched the
    Python model on O0, O2 and Yul, on Anvil and in the Lean Hull runner;
  - that admission refuses a `mix` use with a marker, a marker with steps, a
    subclass method without the unary base method, a subclass impl over no
    base impl, a chain impl over no subclass impl, subclass and chain impls
    out of order, a missing or ill-formed subclass arm, a `top` use without
    the chain's impls, a subclass bound without the subclass impl, a `mix`
    use with one argument, two equal arguments, a shift or a `sub` or
    `function` call, arguments on a base method, an argument four levels
    deep, a binary use without a shift, an unneeded helper, a `function` use
    without its `sub` helper, a generic declaration used as plain and seven
    uses;
  - the reference against the interpreter on the plans of 200 seeds at twelve
    inputs.

  Generation is deterministic, draws every shape value within 300 seeds and
  replays exactly, also with seeded inputs and the identity filter, and a
  256-node budget drops uses. Tampering is refused, and every kind of
  reduction applies, is strictly smaller and replays.
- A fixed corpus of 104 cases from thirteen seeds between 2 and 84, covering
  every shape value; four of the first 84 seeds were excluded and 37 skipped
  for a frontend-rejected `top` use.

Frozen matrices at `68ead60e4` (the freeze digest did not change), under
load averages of 5 to 17 from other work on the machine:
- The fixed corpus matched all 104 cases on O0 and O2 with complete shape and
  input coverage, compiling 13 sources, in 214 and 224 seconds. On Yul, 96
  matched and the eight cases of seed 9 were rejected by solc with a
  `StackTooDeepError`, in 416 seconds; the matched cases still cover every
  shape value and input.
- Random suites from root seed 1 with eight whole functions took eight
  attempts without an exclusion and drew 96 cases from 8 sources in four
  generation requests, after two output-limit retries. They drew every shape
  value except a plain enum as `sc_mix`'s receiver and as a generic argument,
  and Word and plain arguments of `sc_mix`. On O0, O2 and Yul alike, 72
  matched, in 204, 200 and 244 seconds, and the checked frontend rejected
  the 24 cases of two functions with `SC0406` "no unique dictionary", each
  plan having a base-method `top` use at a sum or a generic enum.
- Automatic reduction kept the fingerprint with one binary use through
  `function` for the Yul rejection, whose `Sc_Fold.sc_both` at `Sc_T0<word>`
  solc rejects, as in one of `runtime-traits`' reductions, and with one
  unary `top` use at `sum<word, word>` for one frontend rejection; the
  shared budget of 16 attempts ended the other's reduction. The rejections
  are recorded locally without investigation, so the fixed Yul and random
  gates did not pass; no mismatch was found.

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

**Multi-word return values.** Every other stateful profile returns one Word.
Both contract entry conventions of original Core, `returnWord` and
`wordOutcomeV1`, decode a result into exactly one Word of return data (see the
ninth extension above). The `stateful-tuple-returns` profile returns a static
ABI tuple of two to four Words and compares the whole return data on all three
paths. The user approved a new entry convention in the shared contract
runtime, on one condition: every existing consumer still goes through.

A probe came first. Three hand-written contracts, one per arity, ran
`run(uint256 flags, uint256 input)` with the return types `(uint256, uint256)`,
`(uint256, uint256, uint256)` and `(uint256, uint256, uint256, uint256)`, over
three transactions, one of them reverting. Their tuples mixed a computed Word
with slots read before and after writes. The results:
- The pinned compiler accepted the three return types and their tuple
  expressions. std's `do_exec` encodes the returned value, nested pairs, with
  `abi_encode`, whose static pair encoding concatenates the heads.
- Checked Hull export, Sonatina O0 and O2 images, and Yul through the pinned
  solc all compiled.
- On Anvil, O0, O2 and Yul returned exactly 64, 96 and 128 bytes, the static
  tuple encoding, and reverted with one Word. Imported Hull with O0 and O2
  images gave the same bytes, reverts and slots.
- The storage adapter's EVM path reads the trace's whole `returnValue`, and
  the declared-slot Hull runner prints the whole return data. Neither changes.

So the profile is feasible. The runtime gains one convention and no other
interface:
- **Convention:** `CoreContractEntryProfile.wordTupleOutcomeV1 extraWords`, a
  static tuple of `extraWords + 2` Words.
  - Its result type is `.sum T (.sum .word .word)`, where `T` is the
    right-nested product of the Words. `ofResultType?` recognizes exactly
    these types, and `resultType` stays injective.
  - A returned tuple decodes to the concatenated big-endian bytes of its
    Words. Revert and trap decode as for `wordOutcomeV1`.
  - `CheckedCoreContract.wordTupleOutcomeV1` binds checked code to it.
  - The top-level runner already decodes through `decode?` into bytes, so it
    runs tuple contracts unchanged.
- **One-Word premise:** `CoreContractEntryProfile.returnsOneWord` holds for
  `returnWord` and `wordOutcomeV1`.
  - The Word view, `decodeWordOutcome?` and its lemmas, takes it as a premise.
    A tuple has no one-Word view, and `decodeWordOutcome?` returns `none` for
    it.
  - Those statements gain only that premise. Every statement about
    `returnWord` and `wordOutcomeV1` stays as it is.
- **Nested boundary:** the one-level nested executor resolves a child, or a
  creation template's initializer, only when its convention returns one Word,
  because a nested word call carries exactly one Word of child return data.
  - A registered tuple contract is `unavailable` to a word call, and a
    template with a tuple initializer is `unavailable` to creation. The
    parent's context stays unchanged, as for an unregistered target or
    template.
  - Child and initializer frames carry that evidence, and `startChild` and
    `startInitializer` take it as a premise.
  - No existing environment registers a tuple contract, so no existing
    execution changes.
- The Hull importer, Core's semantics and host requests, and every backend
  stay as they are.

The profile's definitions were fixed before execution:
- **Contract:** `SynthesizedTupleReturns` with
  `run(uint256 flags, uint256 input)`, selector `0x7357f5d2`. It returns `n`
  uint256 Words, with `n` in {2, 3, 4}, and every transaction is zero-value.
- **Arity:** generation draws `n` per scenario by a SplitMix64 hash of the
  seed, and the plan records it.
- **Declared slots 0 to 2:**
  - slot 0, an accumulator;
  - slot 1, the committed call count;
  - slot 2, the last committed input.
- **Transaction:**
  - it reads `prior = slot 0` and `last = slot 2`;
  - it computes `r = step(prior + input)`, where the sum wraps;
  - it writes `r` to slot 0, slot 1 plus one to slot 1, and the input to
    slot 2.

  Odd flags then revert with the one Word `r`. Even flags return the first
  `n` of these Words:
  1. `r`, the computed step result;
  2. slot 1, read back after its write;
  3. `prior`, slot 0 read before its write;
  4. `last`, slot 2 read before its write: the input of the last committed
     transaction.
- **Source** (`solcore-source-tuple-returns-v1`):
  - the step is `sc_step`, rendered by the aggregate renderer;
  - the method's return type is the tuple of `n` uint256;
  - it returns a tuple expression of `uint256(...)` conversions, and Word 2
    is `sload(1)` in that expression.
- **Original Core** (`core-tuple-return-contract-v1`, entry
  `wordTupleOutcomeV1 (n - 2)`): one host contract whose result is `inLeft`
  of the right-nested pairs of the `n` Words, or `inRight (inLeft r)`.
- **Node budget:**
  - the shell, everything but the step, lies inside the budget;
  - the suite's default is 384 nodes, and the doubled budget is capped at
    512;
  - contracts are bounded by 512 nodes.
- **Step:** one checked aggregate step with one to three helpers, generated
  as for the other storage-family profiles. The step must not give equal
  outputs at all boundary inputs.
- **Transactions:** `{id, flags, input, calldata, value}`, one to eight per
  scenario, drawn in blocks of three from a separate stream (mixed since
  `tuple-sequence-seed-v2`; see "Mixed sequence seeds" below). Each block
  draws:
  - three flags from the boundary bank, each with the parity of one of the
    four completion patterns;
  - three inputs from the bank.

  Random runs generate the step with G0 revision three.
- **Observations:** status, the whole return data, slots 0 to 2 and the whole
  committed storage, per prefix.
  - The adapter's output rule for this profile is `32n` bytes on return and
    32 on revert. The rule for every other profile stays one Word.
  - Each returned row must follow the protocol: Word 1 is the committed slot
    0, Word 2 the committed slot 1 and the prior slot 1 plus one, Word 3 the
    prior slot 0, Word 4 the prior slot 2, and the committed slot 2 is the
    input.
  - A revert keeps the prior slots and the whole storage.
- **Exclusions, in order:**
  - a node budget too small for the shell or above 512;
  - the step's own exclusions;
  - a step whose boundary outputs agree;
  - Core fuel exhaustion (resource);
  - a history that does not follow its prescribed parities.
- **Reductions,** each sealed and strictly smaller in transactions, then
  arity, then program size, then transaction values:
  - one-transaction removals;
  - a lower arity (3, then 2), which drops trailing Words and keeps the
    effects;
  - step reductions;
  - simpler transactions: flags to their parity bit, then the input to its
    low byte.
- **Fixed corpus coverage:**
  - arities 2, 3 and 4, each with both outcomes;
  - generated entries at both node budgets, 384 and 512;
  - Words 3 and 4 carrying values that an earlier committed transaction
    wrote, and a revert whose writes a later transaction must not see;
  - one to three helpers and one to three transactions;
  - the six boundary inputs, and the step features, templates and completion
    patterns of its steps.
- **Golden cases** come before any random run:
  - The steps add a constant, and the expected rows, the whole return data
    and the slots, are written out by hand. They cover each arity, both
    outcomes, carries across transactions and wrapping sums.
  - A Lean model of the source, a slot map, must equal the Core contract on
    generated cases.
  - Runtime golden tests check the exact bytes of the convention for two,
    three and four Words, and its revert and trap branches.
- **Out of scope:** dynamic return values (`bytes`, `uint256[]`), tuples with
  dynamic or nested elements, gas, value, other methods and malformed
  calldata.

**Results.** The checks before any random run:
- The runtime golden tests passed. They cover:
  - the exact bytes of two-, three- and four-Word tuples, against
    hexadecimal text, and the revert and trap branches;
  - wrong annotations, arities and payloads, which do not decode;
  - a word call to a registered tuple contract and a creation from a tuple
    initializer, both unavailable;
  - a tuple root, which returns its whole tuple through the nested executor.
- The golden cases passed on both the Core contract and the source model; a
  changed Word fails.
- The model equalled the Core contract on 392 transactions of 64 generated
  scenarios, and every case and reduction replayed.
- The shells take 79, 85 and 91 nodes for arities 2, 3 and 4, so the default
  budget leaves 305 to 293 nodes for the step.
- The gate passed on `ad4c50bdb` alone and on `558f20425`: the full Lean build
  and tests, the kernel check, 724 Python tests, every corpus check and the
  diff check.

The matrices ran on `558f20425` with 136 digests frozen: the files of
`scripts/`, the 28 native tools, solc, Anvil, and the Rust driver and
code-image exporter. None changed during any run, and all 362 case results
record that revision with no tracked difference.
- **Fixed corpora:**
  - O0: all nineteen stateful corpora matched, 242 scenarios and 664 prefixes,
    in 1,827 seconds. The eighteen earlier ones kept their 230 scenarios and
    632 prefixes. They include both call profiles, whose children now pass
    the one-Word admission.
  - The new corpus matched its 12 scenarios and 32 prefixes with complete
    coverage on O0, O2 and Yul, O2 in 68 seconds and Yul in 119:
    - arities 2, 3 and 4, each with both outcomes: 21 returned and 11
      reverted transactions;
    - both node budgets;
    - a returned tuple after an earlier committed transaction in nine
      scenarios, and after a revert in eight.
- **Random suites:** root seed `20261029`, sixteen eight-transaction
  scenarios with G0 revision three, at 384 and 512 nodes on O0, O2 and Yul.
  Every run matched 16 scenarios and 128 prefixes:
  - arities 2, 3 and 4 drawn 4, 6 and 6 times;
  - 92 returned tuples, 22, 39 and 31 by arity, and 36 reverts, 10, 9 and
    17;
  - every scenario returned a tuple after an earlier committed transaction,
    and 15 after a revert;
  - 16 attempts and no exclusion;
  - the two budgets draw the same arities and transactions, and the step
    differs in 13 of the 16 cases.

A random run took 98 to 117 seconds on Sonatina and 173 to 183 on Yul. There
was no finding. Hosted CI has not run the profile.

**Dynamic return values** were probed after the static profile matched, and
not built:
- The pinned compiler's ABI check accepts only `memory<string>` and
  `memory<bytes>` as dynamic public types; it rejects a
  `memory<DynArray<uint256>>` return (SC0231).
- A `memory<bytes>` return of `input & 63` bytes ran identically on every
  path: on Anvil, O0, O2 and Yul returned the canonical encoding (offset 32,
  the length, the data zero-padded to whole Words), and imported Hull with O0
  and O2 images gave the same bytes, reverts and slots.
- Original Core has no variable-length value. A `bytes` result would need a
  Core representation for variable-length data:
  - a recursive data type of Words in `dataDefinitions`. The convention would
    then have to pin the data definitions as well as the result type, which
    `CheckedCoreContract` admission cannot express without another runtime
    change;
  - or a bounded sum with one variant per exact length up to a fixed bound.
    It needs no new Core data, but its decoder must zero the padding bytes of
    every typed value, as std's encoder does, and it takes 65 variants for 64
    bytes.

  Either is a decision of its own, so it is reported here instead of built.

**Bounded `bytes` returns.** The bounded option was then taken up as its own
unit: the `stateful-bytes-returns` profile returns a `memory<bytes>` value of
zero to 64 bytes and compares the whole return data on all three paths. The
condition is the same as for tuples: every existing statement keeps its form,
except for the one-Word premise already introduced, and the nested boundary
stays.

A probe came first. One hand-written contract ran
`run(uint256 flags, uint256 input, uint256 length)`, selector `0x24b912e5`,
returning `memory<bytes>`. It followed the protocol below with the stand-in
step `3x + 7`, over thirteen transactions:
- lengths 0, 1, 31, 32, 33, 63 and 64, and 65 and 100, which the contract
  reads modulo 65;
- two reverts, then returns after them;
- the inputs `2^256 - 1` and `2^255`.

Its data Words are built from products with a fixed odd constant, so the bytes
after the length are not zero in memory. The results:
- The pinned compiler accepted the return type. The method allocates three
  Words with std's `allocate_memory`, stores the length and two data Words
  with `mstore` and returns the pointer. std's `do_exec` encodes it with
  `abi_encode`: `encodeIntoFromBytesLike` writes the offset, copies the
  length and the data with `mcopy` and zeroes the padding with
  `zeroize_memory`.
- Checked Hull export, Sonatina O0 and O2 images, and Yul through the pinned
  solc all compiled.
- On Anvil, O0, O2 and Yul returned exactly `64 + 32⌈L/32⌉` bytes for length
  `L`: the offset 32, the length, the first `L` data bytes and zeros. They
  reverted with one Word. Imported Hull with O0 and O2 images gave the same
  bytes, reverts and slots, in two scenarios of eight calls, the declared-slot
  runner's limit. Every path equalled an independent Python model.

So the profile is feasible on every compiled path, and the bytes after the
length are zero on all of them. The Core representation had to be compact:
- One variant per exact length does not fit. Core counts type annotations as
  program nodes, so such a sum takes 193 nodes. A contract names it in its
  result type and again in its revert injection, so types alone take 390
  nodes, more than the default budget of 384.
- So the runtime gains one convention and no other interface:
  `CoreContractEntryProfile.boundedBytesOutcomeV1`.
  - Its result type is `.sum B (.sum .word .word)` with
    `B = .sum .unit (.product .word (.product .word .word))`, eleven nodes.
    `inLeft unit` is the empty value. `inRight (tag, d0, d1)` is the value
    of length `tag mod 64 + 1`, whose data are the first bytes of the
    big-endian `d0` and `d1`.
  - Every Word tag names one of the lengths 1 to 64, so every typed value
    decodes. The data bytes after the length are ignored.
  - A returned value decodes to std's canonical encoding: the Word 32, the
    length Word, the data, and zeros up to a whole number of Words. Revert
    and trap decode as for `wordOutcomeV1`, under the exact annotation `B`.
  - `ofResultType?` recognizes exactly this type. `B` is a sum, so no
    existing recognition changes, and `resultType` stays injective.
  - `CheckedCoreContract.boundedBytesOutcomeV1` binds checked code to it.
  - The top-level runner decodes through `decode?` into bytes, so it runs
    bytes contracts unchanged.
- **One-Word premise:** `returnsOneWord` is false for the new convention, so
  the Word view rejects it and the nested executor keeps it out. A registered
  bytes contract is `unavailable` to a word call, and a template with a bytes
  initializer is `unavailable` to creation, exactly as for tuples. Neither
  the nested executor nor any existing statement changes.
- The Hull importer, Core's semantics and host requests, and every backend
  stay as they are.

The profile's definitions were fixed before execution:
- **Contract:** `SynthesizedBytesReturns` with
  `run(uint256 flags, uint256 input, uint256 length)`, selector
  `0x24b912e5`, returning `memory<bytes>`. Every transaction is zero-value.
- **Length:** each transaction records its length `L` from 0 to 64, and the
  contract reads the length Word modulo 65.
- **Declared slots 0 to 2,** as for tuples:
  - slot 0, an accumulator;
  - slot 1, the committed call count;
  - slot 2, the last committed input.
- **Transaction:**
  - it reads `prior = slot 0` and `last = slot 2`;
  - it computes `r = step(prior + input)`, where the sum wraps;
  - it writes `r` to slot 0, slot 1 plus one to slot 1, and the input to
    slot 2.

  Odd flags then revert with the one Word `r`. Even flags return the first
  `L` bytes of the two data Words:
  1. `d0 = r · K`;
  2. `d1 = (count · K) xor last`, where `count` is slot 1 read back after its
     write.

  `K` is the odd constant
  `0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95`, and
  products wrap. Multiplying by `K` makes the leading bytes depend on the
  whole Word, so short values carry data and the bytes after the length are
  rarely zero.
- **Source** (`solcore-source-bytes-returns-v1`):
  - the step is `sc_step`, rendered by the aggregate renderer;
  - the method's return type is `memory<bytes>`;
  - it allocates 96 bytes with `allocate_memory`, stores `L`, `d0` and `d1`
    with `mstore`, and returns the pointer through `Typedef.abs`;
  - `d1` reads `sload(1)` after the writes.
- **Original Core** (`core-bytes-return-contract-v1`, entry
  `boundedBytesOutcomeV1`): one host contract whose result is
  `inLeft (inLeft unit)` for an empty value,
  `inLeft (inRight (L - 1, d0, d1))` otherwise, or `inRight (inLeft r)`.
- **Node budget:**
  - the shell, everything but the step, lies inside the budget;
  - the suite's default is 384 nodes, and the doubled budget is capped at
    512;
  - contracts are bounded by 512 nodes.
- **Step:** one checked aggregate step with one to three helpers, generated
  as for the other storage-family profiles. The step must not give equal
  outputs at all boundary inputs.
- **Transactions:** `{id, flags, input, length, calldata, value}`, one to
  eight per scenario, drawn in blocks of three from a separate stream (mixed
  since `bytes-sequence-seed-v2`; see "Mixed sequence seeds" below). Each
  block draws:
  - three flags from the boundary bank, each with the parity of one of the
    four completion patterns;
  - three inputs from the bank;
  - three lengths, each from the length bank 0, 1, 31, 32, 33, 63 and 64
    with probability one half, otherwise uniformly from 0 to 64.

  Random runs generate the step with G0 revision three.
- **Observations:** status, the whole return data, slots 0 to 2 and the whole
  committed storage, per prefix.
  - The adapter's output rule for this profile is `64 + 32⌈L/32⌉` bytes on
    return and 32 on revert. The rule for every other profile stays as it
    is.
  - Each returned row must follow the protocol: the Word 32, the length Word
    `L`, the first `L` bytes of `d0` and `d1` from the committed slots 0 and
    1 and the prior slot 2, then zero bytes. Slot 1 grows by one, and the
    committed slot 2 is the input.
  - A revert keeps the prior slots and the whole storage.
- **Exclusions, in order:**
  - a node budget too small for the shell or above 512;
  - the step's own exclusions;
  - a step whose boundary outputs agree;
  - Core fuel exhaustion (resource);
  - a history that does not follow its prescribed parities.
- **Reductions,** each sealed and strictly smaller in transactions, then the
  total length, then program size, then the flags and inputs:
  - one-transaction removals;
  - shorter lengths: zero, then half the length;
  - step reductions;
  - simpler transactions: flags to their parity bit, then the input to its
    low byte.
- **Fixed corpus coverage:**
  - returned lengths 0, 1, 31, 32, 33, 63 and 64;
  - empty, partial-Word and whole-Word lengths, each with both outcomes;
  - generated entries at both node budgets, 384 and 512;
  - a returned value after an earlier committed transaction, and after a
    revert whose writes it must not see;
  - one to three helpers and one to three transactions;
  - the six boundary inputs, and the step features, templates and completion
    patterns of its steps.
- **Golden cases** come before any random run:
  - The steps add a constant, and the expected rows, the whole return data
    and the slots, are written out as hexadecimal text. They cover the bank's
    seven lengths, both outcomes, carries across transactions and wrapping
    sums.
  - A Lean model of the source, a slot map and std's copy-and-zero encoder
    over the method's memory, must equal the Core contract on generated
    cases.
  - Runtime golden tests check the exact bytes of the convention for lengths
    0, 1, 31, 32, 33 and 64, with nonzero bytes after the length, and its
    revert and trap branches.
- **Out of scope:** `bytes` returns beyond 64 bytes, strings, array returns,
  lengths above 64 in a case, tuples with dynamic elements, gas, value, other
  methods and malformed calldata.

**Results.** The checks before any random run:
- The runtime golden tests passed. They cover:
  - the exact bytes of lengths 0, 1, 31, 32, 33 and 64 against hexadecimal
    text, with nonzero data bytes after each length, all-ones data cut at 33
    bytes, and tags that wrap modulo 64;
  - the revert and trap branches, and wrong annotations and payloads, which
    do not decode;
  - a word call to a registered bytes contract and a creation from a bytes
    initializer, both unavailable;
  - a bytes root, which returns its whole encoding through the nested
    executor.
- The golden cases passed on both the Core contract and the source model. A
  corpus row with a nonzero padding byte, a changed head Word or a shorter
  output is rejected.
- The model equalled the Core contract on 392 transactions of 64 generated
  scenarios. Every case and reduction replayed, and generation drew every
  bank length.
- The shell takes 125 nodes, so the default budget leaves 259 for the step.
- A synthetic slot-0 difference on imported Hull reduced from three
  transactions to one of length 1 in 12 attempts. The campaign's synthetic
  output adapter changes only a one-Word output, so it does not apply here.
- The gate passed on `e41787d2e` and on `93e26b3b3`: the full Lean build and
  tests, the kernel check, 737 and then 743 Python tests, every corpus check
  and the diff check, with 29 and then 30 native tools.

The matrices ran on `93e26b3b3` with 141 digests frozen: the files of
`scripts/`, the 30 native tools, solc, Anvil, and the Rust driver and
code-image exporter. None changed during any run, and all 387 case results
record that revision with no tracked difference.
- **Fixed corpora:**
  - O0: all twenty-one stateful corpora matched, 267 scenarios and 729
    prefixes, in 2,296 seconds. The twenty earlier ones kept their 255
    scenarios and 697 prefixes, both call profiles included.
  - The new corpus matched its 12 scenarios and 32 prefixes with complete
    coverage on O0, O2 and Yul, O2 in 127 seconds and Yul in 120:
    - the returned lengths 0, 1, 16, 27, 31, 32, 33, 58, 63 and 64;
    - 23 returned and 9 reverted transactions over the empty, partial-Word
      and whole-Word lengths;
    - both node budgets;
    - a returned value after an earlier committed transaction in nine
      scenarios, and after a revert in six.
- **Random suites:** root seed `20261030`, sixteen eight-transaction
  scenarios with G0 revision three, at 384 and 512 nodes on O0, O2 and Yul.
  Every run matched 16 scenarios and 128 prefixes:
  - 98 returned values of 39 distinct lengths, all seven bank lengths among
    them, and 30 reverts;
  - of the returned values, 7 were empty, 79 ended in a partial Word and 12
    filled whole Words;
  - every scenario returned a value after an earlier committed transaction,
    and 15 after a revert;
  - 16 attempts and no exclusion;
  - the cases were identical on the three backends at each budget, the two
    budgets draw the same transactions, and the step differs in 15 of the 16
    cases.

A random run took 103 to 114 seconds on Sonatina and 170 to 176 on Yul. There
was no finding. Hosted CI has not run the profile.

**Returned enums.** Every generated program so far returns Words, std pairs or
std sums. User-defined `enum` types and their ABI encoding through
`std.ABIGeneric` are untested, and the pinned checkout's own fixtures place
front-end defects there: `abi-dyn-sum-return` records that the generic encoder
once wrote only the tag of a returned dynamic enum. The
`stateful-enum-returns` profile returns a value of an enum of two to four
constructors and compares the whole return data on all three paths. The
condition is the same as for tuples and `bytes`: every existing statement
keeps its form, except for the one-Word premise already introduced, and the
nested boundary stays.

std's encoding, from `std/ABIGeneric.sol` and the compiler's derived
instances:
- An enum crosses the ABI with one tag Word per constructor,
  `keccak256("Name(fields)")`. `fields` is std's `sigStr` of the
  constructor's fields: empty, `uint256`, `uint256,uint256` or `bytes`.
- A static enum, one without a `bytes` field, is inline: the tag, then the
  fields. Its head is the tag Word and the widest constructor's fields, so a
  narrower constructor leaves the rest of the head unwritten.
- A dynamic enum is the offset Word 32, then that body. A `bytes` field's head
  Word is its offset from the body's start, the body's head, and its tail is
  std's `bytes` encoding: the length Word and the zero-padded data.

A probe came first: eight hand-written contracts with
`run(uint256 flags, uint256 input, uint256 choice, uint256 length)`, selector
`0x15509d2b`, each returning one enum.
- Four were static: `Nil | Single(uint256)`,
  `Wide(uint256, uint256) | Empty | Narrow(uint256) | Idle`,
  `Lone(uint256) | PairA(uint256, uint256) | PairB(uint256, uint256)` and
  `Off | On`.
- Four were dynamic: `Value(uint256) | Data(bytes) | Gone`,
  `Nil | Single(uint256) | Double(uint256, uint256) | Blob(bytes)`,
  `Left(bytes) | Right(bytes) | Both(uint256, uint256)` and
  `Head(bytes) | Tail(uint256)`.
- Each ran eight transactions of the protocol below. They returned every
  constructor, with `bytes` lengths 0, 1, 9, 31, 32, 33, 35, 63 and 64. They
  included a revert with returns after it, choices and lengths beyond the
  constructor count and 64, which the contract reads modulo the count and 65,
  and the inputs `2^256 - 1` and `2^255`.
- Each contract ran with the stand-in step `3x + 7`, then with two generated
  G0 revision-three steps of pairs, sums, matches and cells: 24 contracts and
  192 transactions.

The results:
- The pinned compiler accepted every shape as a public return type. Checked
  Hull export, Sonatina O0 and O2 images, and Yul through the pinned solc all
  compiled.
- On Anvil, O0, O2 and Yul returned the same bytes and reverted with one Word.
  Imported Hull with O0 and O2 images gave the same bytes, reverts and slots:
  960 path runs in all.
- Every output equalled an independent Python model of the encoding above,
  with the tags computed by `cast keccak`. The model fills the unwritten head
  Words with zeros. They are zero on every path because std's encoder starts
  at the free-memory pointer, and nothing in these methods writes above it.

So the profile is feasible on every compiled path. The Core representation:
- **One convention:** `CoreContractEntryProfile.enumOutcomeV1 first second
  rest`. It records the constructors' fields in declaration order, each an
  `EnumPayload`: `noWords`, `oneWord`, `twoWords` or `boundedBytes`.
- **Tags in the value:** a convention that recorded the tags would not be
  determined by its result type. `ofResultType?` and the injectivity of
  `resultType` would then have to change, so the value carries them.
  - Each constructor's value is its tag Word paired with its fields: `(tag,
    ())`, `(tag, w)`, `(tag, (w0, w1))` or `(tag, b)`. Here `b` is the
    bounded `bytes` value of `boundedBytesOutcomeV1`.
  - The returned value is the right-nested sum of these in declaration order.
- **Decoding:** `decode?` maps a returned value to std's encoding:
  - the tag, the fields' head, zero Words up to the body's head, then a
    `bytes` field's length Word and zero-padded data;
  - for a dynamic enum, the offset Word 32 first;
  - revert and trap as for `wordOutcomeV1`, under the exact enum annotation.

  Every annotation is strict, and every typed value decodes.
- **Recognition:** `ofResultType?` recognizes exactly these types, after the
  earlier conventions. Every constructor's value is a product whose first
  component is a Word, so no existing type changes its recognition, the
  existing rejections stay, and `resultType` stays injective.
- **Binding:** `CheckedCoreContract.enumOutcomeV1` binds checked code to it.
  The top-level runner decodes through `decode?` and runs enum contracts
  unchanged.
- **One-Word premise:** `returnsOneWord` is false for every enum, even one of
  field-less constructors, whose encoding is one Word. So the nested executor
  keeps every enum contract out: a registered enum contract is `unavailable`
  to a word call, and a template with an enum initializer is `unavailable` to
  creation. Neither the nested executor nor any existing statement changes.
- The Hull importer, Core's semantics and host requests, and every backend
  stay as they are.

The profile's definitions were fixed before execution:
- **Contract:** `SynthesizedEnumReturns` with
  `run(uint256 flags, uint256 input, uint256 choice, uint256 length)`,
  selector `0x15509d2b`, returning the source enum `SynthesizedEnum`. Every
  transaction is zero-value.
- **Shape:** each case records its enum's constructors in declaration order.
  - There are two to four, each named from the bank `Idle`, `Ready`, `Pair`,
    `Blob`, `Settled`, `Q`, `Rejected` and `OverflowedAccumulator` without
    repetition.
  - Each has no fields, one `uint256`, two `uint256`s or one
    `memory<bytes>`. At most two carry `bytes`.
  - A shape without `bytes` is static, any other is dynamic.
- **Choice and length:** each transaction records its constructor index `c`,
  below the constructor count `n`. It also records `L`, from 0 to 64 when
  constructor `c` carries `bytes` and 0 otherwise. The contract reads the
  choice Word modulo `n` and the length Word modulo 65.
- **Declared slots 0 to 2,** as for tuples and `bytes`: an accumulator, the
  committed call count and the last committed input.
- **Transaction:** as for `bytes`, it reads `prior = slot 0` and
  `last = slot 2`, computes `r = step(prior + input)` and writes `r`, slot 1
  plus one and the input. Odd flags then revert with the one Word `r`. Even
  flags return constructor `c` with its fields:
  1. none;
  2. `d0 = r · K`;
  3. `(d0, d1)`, with `d1 = (count · K) xor last`;
  4. the first `L` bytes of `d0` and `d1`.

  `K` and `count` are as for `bytes`.
- **Source** (`solcore-source-enum-returns-v1`):
  - it imports `std.Generic` and `std.ABIGeneric` beside `std` and
    `std.dispatch`, and declares `enum SynthesizedEnum` with the shape's
    constructors;
  - the step is `sc_step`, rendered by the aggregate renderer;
  - the method computes `d0` and `d1` after the writes, then tests the choice
    against each constructor index but the last and returns that
    constructor;
  - a `bytes` constructor allocates 96 bytes with `allocate_memory`, stores
    `L`, `d0` and `d1` with `mstore`, and passes the pointer through
    `Typedef.abs` as a `memory<bytes>` local.
- **Original Core** (`core-enum-return-contract-v1`, entry
  `enumOutcomeV1`): one host contract whose result is `inLeft v` for
  constructor `c`'s value `v`, or `inRight (inLeft r)`.
  - Each tag is `keccak256("Name(fields)")`, computed by Lean's Keccak-256.
  - The contract binds `d0`, `d1` and, for a dynamic shape, the `bytes`
    value.
  - Then one test of `c` per constructor injects that constructor left of
    the remaining ones, or passes right.
- **Node budget:**
  - the shell, everything but the step, depends on the shape: 130 to 191
    nodes for two constructors, 157 to 238 for three and 188 to 291 for four;
  - it lies inside the budget, so the 384-node default leaves 93 to 254
    nodes for the step;
  - the doubled budget is capped at 512, and contracts are bounded by 512
    nodes.
- **Step:** one checked aggregate step with one to three helpers, generated as
  for the other storage-family profiles. The step must not give equal outputs
  at all boundary inputs. A step budget too small for the drawn template is an
  exclusion, which large shapes at 384 nodes meet more often.
- **Shape generation:** a stream of its own draws, in order:
  1. the constructor count, uniformly from 2 to 4;
  2. zero `bytes` constructors with probability one half, otherwise one or
     two with probability one quarter each;
  3. each other constructor's fields, uniformly from none, one Word and two
     Words;
  4. the positions of the `bytes` constructors;
  5. the names, drawn from the bank without repetition.
- **Transactions:** `{id, flags, input, choice, length, calldata, value}`, one
  to eight per scenario, drawn in blocks of three from a separate stream. Each
  block draws:
  - three flags from the boundary bank, each with the parity of one of the
    four completion patterns;
  - three inputs from the bank;
  - three choices, uniformly below `n`;
  - three lengths, used only for `bytes` constructors. Each is from the
    length bank 0, 1, 31, 32, 33, 63 and 64 with probability one half,
    otherwise uniformly from 0 to 64.

  Random runs generate the step with G0 revision three.
- **Observations:** status, the whole return data, slots 0 to 2 and the whole
  committed storage, per prefix.
  - The adapter's output rule: let `w` be the widest constructor's field head,
    0, 32 or 64 bytes, where `bytes` counts 32. A static enum returns
    `32 + w` bytes. A dynamic one returns `64 + w`, plus `32 + 32⌈L/32⌉`
    for a `bytes` constructor. A revert returns 32. The rule for every other
    profile stays as it is.
  - Each returned row must follow the protocol: constructor `c`'s tag, its
    fields from the committed slots 0 and 1 and the prior slot 2, zero
    padding, and for a dynamic enum the offset Words and the `bytes` tail.
    Slot 1 grows by one, and the committed slot 2 is the input.
  - A revert keeps the prior slots and the whole storage.
- **Exclusions, in order:**
  - a node budget too small for the shell or above 512;
  - the step's own exclusions;
  - a step whose boundary outputs agree;
  - Core fuel exhaustion (resource);
  - a history that does not follow its prescribed parities.
- **Reductions:** each candidate is sealed and strictly smaller in
  transactions, then the shape's weight, then the total length, then program
  size, then the flags and inputs. A shape's weight sums one per constructor
  and its fields' weight: 0, 1, 2 and 3 for none, one Word, two Words and
  `bytes`. The reductions, in order:
  - one-transaction removals;
  - shorter lengths: zero, then half the length;
  - a constructor that no transaction chooses, dropped while more than two
    remain; the choices above it move down;
  - narrower fields: two Words to one, one Word to none, and `bytes` to none
    with the lengths of its transactions set to zero;
  - step reductions;
  - simpler transactions: flags to their parity bit, then the input to its
    low byte.
- **Fixed corpus coverage:**
  - constructor counts 2, 3 and 4, with every position of each returned;
  - static enums returning each of no fields, one Word and two Words, and
    dynamic enums returning each of the four field kinds;
  - padded and full-width returns, in static and in dynamic enums;
  - returned `bytes` lengths 0, 1, 31, 32, 33, 63 and 64;
  - a shape with two `bytes` constructors;
  - both outcomes and both node budgets, 384 and 512;
  - a returned value after an earlier committed transaction, and after a
    revert whose writes it must not see;
  - one to three helpers, the six boundary inputs, and the step features,
    templates and completion patterns of its steps.
- **Golden cases** come before any random run:
  - The steps add a constant, and the expected rows, the whole return data
    and the slots, are written out as hexadecimal text. They cover static and
    dynamic shapes, every field kind, padding, the bank's seven lengths, both
    outcomes, carries across transactions and wrapping sums.
  - A Lean model of the source must equal the Core contract on generated
    cases. It is a slot map and std's `abi_encode` of the enum over a byte
    memory: `encodeVariant`, the pair, `uint256` and unit encoders, and
    `encodeIntoFromBytesLike`.
  - Runtime golden tests check the convention's exact bytes for every field
    kind in static and dynamic shapes, padding Words, and `bytes` lengths 0,
    1, 31, 32, 33 and 64 behind body heads of two and three Words and in first
    position. They also check its revert and trap branches.
- **Synthetic output adapter:** the campaign's `--test-field output` adapter
  flips the low bit of a returned output's last Word, for any output of whole
  Words. A one-Word output changes exactly as before, and the tuple, `bytes`
  and enum returns become reducible from a synthetic output difference.
- **Out of scope:**
  - other field types, generic, nested or recursive enums, and structs;
  - `match` in the method, and enums in calldata or storage;
  - more than two `bytes` constructors, and `bytes` beyond 64 bytes;
  - gas, value, other methods and malformed calldata;
  - a method that writes above the free-memory pointer before it returns, as
    std's `ecrecover` and EIP-712 helpers do. Those bytes would then fill the
    unwritten head Words.

**Results.** The checks before any random run:
- The runtime golden tests passed. They cover:
  - the exact bytes of every field kind in static and dynamic shapes, the
    padding Words, and `bytes` lengths 0, 1, 31, 32, 33 and 64 behind body
    heads of two and three Words and in first position, against hexadecimal
    text;
  - the revert and trap branches, and wrong annotations and fields, which do
    not decode;
  - a word call to a registered enum contract and a creation from an enum
    initializer, both unavailable;
  - an enum root, which returns its whole encoding through the nested
    executor.
- The golden cases passed on both the Core contract and the source model, with
  Lean's Keccak-256 tags equal to those of `cast keccak`; a changed tag is
  detected.
- The model equalled the Core contract on 440 transactions of 76 generated
  scenarios. Every case and reduction replayed, and generation drew every
  constructor count, field kind, position and bank length, and two `bytes`
  constructors.
  - 9 of 85 attempts were excluded at 384 nodes for a step budget too small
    for the drawn template, and none at 512.
  - The first run of this test caught a generator flaw: the draws are affine
    in their start, so over consecutive seeds the raw shape stream alternated
    between static shapes and one `bytes` constructor and never drew two. Both
    streams now start at SplitMix64's finalizer of the seed xor their domain.
- The shells take the 130 to 291 nodes defined above.
- A synthetic output difference, the low bit of the last Word on imported Hull
  at `tx-2` of `dynamic-four-words`, reduced in 12 attempts. Four constructors
  and three transactions became `Blob(bytes) | Rejected` and that one
  transaction with length 0. Narrowing `Blob` changes the finding's payload
  shape, so the shrinker kept its field.
- The fixed corpus has fifteen scenarios and 38 transactions: nine imported
  scenarios over the `bytes` corpus's six imported steps, and six generated
  seeds, three at each budget. The campaign admits imported entries of one to
  three transactions, so a shape's coverage spans entries of one step.
- The gate passed on `24ab8dd3f` alone and on `1dc56407d`: the full Lean build
  and tests, the kernel check, 755 and then 762 Python tests, every corpus
  check and the diff check, with 32 and then 33 native tools.

The matrices ran on `1dc56407d` with 148 digests frozen: the files of
`scripts/`, the 33 native tools, solc, Anvil, and the Rust driver and
code-image exporter. None changed during any run, and all 443 case results
record that revision with no tracked difference.
- **Fixed corpora:**
  - O0: all twenty-four stateful corpora matched, 317 scenarios and 859
    prefixes, in 3,249 seconds. The twenty-three earlier ones kept their 302
    scenarios and 821 prefixes, both call profiles included.
  - The new corpus matched its 15 scenarios and 38 prefixes with complete
    coverage on O0, O2 and Yul, O2 in 226 seconds and Yul in 175:
    - 32 returned and 6 reverted transactions;
    - every position of two, three and four constructors, all seven field
      kinds, and padded and full-width returns in static and dynamic enums;
    - `bytes` returns of lengths 0, 1, 16, 18, 31, 32, 33, 50, 63 and 64,
      from shapes with one and with two `bytes` constructors;
    - a returned value after an earlier committed transaction in 12
      scenarios, and after a revert in 5.
- **Random suites:** root seed `20261031`, sixteen eight-transaction
  scenarios with G0 revision three, at 384 and 512 nodes on O0, O2 and Yul.
  Every run matched 16 scenarios and 128 prefixes:
  - at 384 nodes, 19 attempts and 3 exclusions for a step budget too small
    for the drawn template, all three-helper steps under three or four
    constructors; at 512 nodes, 16 attempts and no exclusion;
  - at each budget, 4 shapes of two constructors, 9 of three and 3 of four;
    10 static and 6 dynamic, 3 of them with two `bytes` constructors;
  - at 384 nodes, 96 returned values and 32 reverts. The returns covered all
    nine positions and all seven field kinds: 59 from static enums, 26 of
    them padded, and 37 from dynamic ones, 14 padded. 20 were `bytes`
    returns of 14 distinct lengths: 2 empty, 17 partial and 1 whole;
  - at 512 nodes, 95 returned values and 33 reverts, over all positions and
    six field kinds; no field-less constructor of a dynamic enum returned.
    57 came from static enums, 23 padded, and 38 from dynamic ones, 18
    padded. 22 were `bytes` returns of 14 distinct lengths: 2 empty, 17
    partial and 3 whole;
  - every scenario returned a value after an earlier committed transaction
    and after a revert, at both budgets;
  - the cases were identical on the three backends at each budget. The 13
    seeds both budgets accepted draw the same shapes and transactions, and
    the step differs in 9 of them.

A random run took 115 to 264 seconds on Sonatina and 211 to 220 on Yul. There
was no finding. Hosted CI has not run the profile.

**Storage and Keccak loops through inline Yul.** `stateful-storage-loops`
and `stateful-keccak-loops` lower `sload`, `sstore`, the mapping's hash and
`log2` through Solcore's own path: std's one-statement wrapper functions,
called from source expressions. The inline Yul path, where the pure profiles
found the Sonatina crash on constant shift counts that Solcore's lowering
never reached, has no stateful case. Two new profiles render the same two
plans with every storage read and write, the entry hash, the log and the
completion in `assembly` blocks of the source:
`stateful-assembly-storage-loops` and `stateful-assembly-keccak-loops`. One
profile per plan keeps each profile's plan, Core reference, observation,
protocol check and reductions exactly those of the profile it renders, plus a
form; one profile for both would carry two plans, two observations and two
reduction sets under one schema.

The pinned front end types a Yul call only as a builtin or as a Yul function
of the enclosing blocks (`hir-ty/src/infer/yul.rs`), so a block cannot call
the Solcore step. The loop therefore stays a Solcore `while` loop, and each
iteration runs its storage, hash and log work in Yul around one Solcore step
call. A Yul `for` loop would need the aggregate step, with its pairs, sums and
cells, rendered as Yul, which is a renderer of its own and outside this unit.

A probe preceded them. It rendered five corpus plans by hand in the three
forms below: the storage-loop plans `seven-counts`, whose step has cells, sums
and conditionals, and `seven-wide`, with pairs, and the Keccak-loop plans
`seven-shared`, `seven-pairs` and `seven-wide`, with key masks 0, 1 and 7. One
storage and one Keccak source also kept the parent's `std.opcodes` import of
the wrappers named like the builtins. Each source ran eight transactions with
0, 1, 2, 3, 5, 6 and 7 iterations, reverts after three and five iterations,
inputs `2^256 - 1` and `2^255 + 5`, and entries reused within and across
transactions. The parent profile's native tool emitted each plan's case and
observed its unchanged Core reference. The results:
- The pinned compiler accepted `sload`, `sstore`, `mload`, `mstore`,
  `keccak256`, `log2` and `revert` with `add`, `sub`, `and`, `or` and `gt` in
  `assembly` blocks of a contract method, reading and assigning Solcore
  locals, in Yul `let`s and under Yul `if`.
- Imported Hull with O0 and O2 images and the EVM on O0, O2 and Yul matched the
  Core reference on status, output, every observed slot and every log, with no
  stray slot: 16 sources and 80 path runs.
- Yul compiled to one creation/runtime pair. Its runtime uses `sload`,
  `sstore`, `mload`, `mstore` and `revert`, and for Keccak loops `keccak256`
  and `log2`, and reads no code.

So neither Core, the shared runtime, the Hull importer, the declared-slot
runner, a backend, `export-rust-yul.py` nor any proof changes. The definitions
were fixed before execution:

- **Contracts:** `SynthesizedAssemblyStorageLoops` and
  `SynthesizedAssemblyKeccakLoops`, each with
  `run(uint256 flags, uint256 input)`, selector `0x7357f5d2`. Each returns
  one uint256, and every transaction is zero-value.
- **Plans:** the parent profile's plan, unchanged, plus a form: a step, the
  loop mask `M` and, for Keccak loops, the key mask `S`, each in
  {0, 1, 3, 7}. The plan schemas `solcore-lean.assembly-storage-loop-plan.v1`
  and `solcore-lean.assembly-keccak-loop-plan.v1` add `form` to the parent
  plan's fields, under the parent's case keys `storageLoopPlan` and
  `keccakLoopPlan`.
- **Generation:** the parent profile's scenario of the seed by the same
  steps: its masks, its step and its transactions. The form comes from a
  SplitMix64 hash of the seed in its own domain and is recorded in the plan
  and the generated origin. A registered Lean test requires each profile to
  agree with its parent for the same seed, budget, G0 revision and
  transaction count on plans, programs, transactions, observations,
  generation records and exclusions.
- **Original Core:** unchanged. The references are
  `core-storage-loop-contract-v1` and `core-keccak-loop-contract-v1` under
  `wordOutcomeV1`, with finite ordinal guards and no counter cell. Their
  observations and history schemas are the parents'
  (`solcore-lean.storage-loop-history.v1` and
  `solcore-lean.keccak-loop-history.v1`).
- **Rendering, in every form:**
  - the step and its helpers render as in the parent profiles, as the
    Solcore functions `sc_fn<k>` and `sc_step`; `std.opcodes` supplies only
    the step's opcode aliases, so the method calls no std storage, hash, log,
    memory or revert wrapper;
  - `run` sets `sc_limit = (sc_input & M)` and, for Keccak loops,
    `sc_base = (sc_input & ~7)` in Solcore, declares its other Word locals as
    zero before the loop, and loops with `while (sc_limit > sc_counter)`;
  - every storage access is a Yul `sload` or `sstore` in an `assembly`
    block, which reads and assigns the Solcore locals;
  - storage loops: iteration `i`'s slot is `add(sc_counter, 2)`, and its
    step argument is
    `add(add(add(add(sload(0), sload(1)), sload(sub(slot, 1))), sload(slot)), sc_input)`;
  - Keccak loops: a block before the loop reserves 64 bytes with
    `sc_ptr := mload(64)` and `mstore(64, add(sc_ptr, 64))`. Iteration `i`'s
    key is `or(sc_base, and(sc_counter, S))`. Its entry slot is
    `keccak256(sc_ptr, 64)` after `mstore(sc_ptr, 1)` and
    `mstore(add(sc_ptr, 32), key)`, std's layout. Its step argument is
    `add(add(sload(entry), sload(0)), sc_input)`, and its log is
    `mstore(sc_ptr, value)` then `log2(sc_ptr, 32, sc_counter, key)`;
  - the writes are `sstore(slot, value)` then `sstore(0, value)`, the
    parents' order;
  - one block after the loop completes:
    - storage loops: `sstore(1, add(sload(1), sc_limit))`, then
      `sc_result := add(sload(0), sload(1))`;
    - Keccak loops: `sc_result := add(sload(0), sc_limit)`;
    - then `if and(sc_flags, 1) { mstore(p, sc_result) revert(p, 32) }`, with
      `p` zero for storage loops, as in the parent, and `sc_ptr` for Keccak
      loops;

    `run` returns `uint256(sc_result)`.
- **Forms:**
  - `split`: each iteration has a read block before
    `sc_value = sc_step(sc_sum);` and a write block after it. The storage read
    block computes the slot in a Yul `let`, and the Keccak read block assigns
    the key to the Solcore `sc_key`. The write block computes the slot again,
    hashing the key again for Keccak loops. The counter advances in Solcore.
  - `carried`: the read block assigns the slot, or the entry slot, to the
    Solcore `sc_slot`, which the write block uses after the step call. The
    write block advances the counter with `sc_counter := add(sc_counter, 1)`.
  - `pipelined`: a block before the loop computes iteration 0's slot and step
    argument under `if gt(sc_limit, sc_counter)`. The loop body is the step
    call and one block. That block writes and logs, advances the counter, and
    then, under `if gt(sc_limit, sc_counter)`, computes the next iteration's
    slot and step argument. A read that depends on the writes just made
    follows them in the same block: storage slot `1 + (i + 1)` and slot 0,
    and, for Keccak loops, an entry that the next key shares.
- **Bounds and node budget:** the parents'. Masks are in {0, 1, 3, 7}, at
  most seven iterations, and the suite's default is 384 nodes:
  - storage loops: the 57-node shell lies inside the budget, the guards
    outside it, and contracts are bounded by 827 nodes;
  - Keccak loops: the 38-node shell lies inside the budget, the Keccak
    closure and the guards outside it, and contracts are bounded by
    512 + 2,654 + 483 nodes.
- **Transactions:** the parents': `{id, flags, input, iterations, calldata,
  value}`, one to eight, drawn in blocks of three, with `iterations` recorded,
  checked on decode and recomputed on replay.
- **Observations:** the parents':
  - storage loops: slots 0 to 8;
  - Keccak loops: slot 0 and the entry slot of every addressed key, derived
    with the independent `Solcore.Abi.V1.Keccak256`, and every committed log
    on all paths;
  - whole storage on Hull and the EVM, with no nonzero undeclared slot.
- **Protocol check** of each returned row: the parents' (the storage-loop
  and Keccak-loop checks).
- **Exclusions:** the parents', in their order, at the stages
  `assembly-storage-loop-profile` and `assembly-keccak-loop-profile`.
- **Reductions:** the parents', each in the parent case's form. A reduced
  case keeps its form, and the strict order is the parent's.
- **Fixed corpora** (`scripts/semantic-assembly-storage-loop-corpus.json`,
  `scripts/semantic-assembly-keccak-loop-corpus.json`):
  - every scenario of the parent's fixed corpus, with the same plan and
    transactions, so the parent's requirements: masks, key masks, iteration
    counts 0 to 7, carries, carried slots, inputs, step features, helper
    counts, templates, transaction counts and completion patterns;
  - the generated seeds stay generated, with their forms by hash, and the
    imported entries take the forms in turn, in corpus order: `split`,
    `carried`, then `pipelined`;
  - in addition, each form runs the parent entries that give it iteration
    counts 0, 1 and 7, every carry and a revert after loop writes:
    `seven-carried` and `seven-counts` for storage loops, and `seven-wide`,
    `seven-shared` and `seven-counts` for Keccak loops;
  - coverage adds `Forms`, `FormIterations` (`form:count` for the counts 0,
    1 and 7) and `FormCarries` (`form:carry` for every carry of the plan),
    recorded for matched cases.
- **Golden tests:**
  - each form's emitted contract for one plan of each profile, written out
    by hand, beside the parent profile's step functions;
  - the parents' hand-written rows, reproduced through the new cases:
    decoding a case and observing its Core reference gives the parent's rows
    in every form;
  - a changed expectation fails.
- **Out of scope:** a Yul `for` loop or a Yul rendering of the step, Yul
  `switch`, `break`, `continue` and Yul functions here (the pure assembly
  profiles cover them), gas, value, other methods and malformed calldata.

**Results.** The checks before any random run:
- The golden tests passed. Each form's contract equals the hand-written text
  for both plans, and the parents' 12 storage and 18 Keccak hand-written rows
  came back through cases of all three forms, slots, entries and logs
  included. A changed expectation failed.
- Generation agreed with the parent profiles on 16 storage and 8 Keccak
  scenarios under G0 revisions three and one: attempts, exclusions, plans,
  programs, transactions, observed slots, origins and observations.
  - Every form was drawn.
  - Every case and the reductions of two cases per profile replayed in their
    form.
  - An unknown form, the parents' schemas and a form that the source was not
    emitted in were refused.
- The corpus tests rebuilt both corpora from the parent corpora, and every
  original Core history equalled the parent's expected history: 16 scenarios
  and 43 transactions, and 19 scenarios, 49 transactions and 137 logs.
- An unfrozen O0 run of both corpora matched with complete coverage.
- The gate passed on the final tree before `1659dc250`: the forbidden-term
  scan, `lake build` (10,232 jobs), 31 native tools prepared offline,
  `lake test` (334 seconds), the kernel check, 770 Python tests, every
  `Tests/scripts` check with the storage-rollback corpus, and the diff check.

The matrices ran on `1659dc250` with 94 digests frozen: the 31 native tools,
every `scripts/*.py` and `*.rs`, solc, Anvil, and the Rust driver and
code-image exporter. None changed during any run, and all 552 case results
record that revision with no tracked difference.
- **Fixed corpora:**
  - O0: all twenty-two stateful corpora matched, 290 scenarios and 789
    prefixes, in 2,291 seconds. The twenty earlier ones kept their 255
    scenarios and 697 prefixes.
  - The two new corpora matched with complete coverage on O0, O2 and Yul:
    storage loops 16 scenarios and 43 prefixes in 102, 142 and 200 seconds,
    and Keccak loops 19 scenarios and 49 prefixes in 144, 177 and 195.
  - Every form ran iteration counts 0, 1 and 7 and every carry. Eight
    transactions of each corpus reverted after loop iterations, and the
    Keccak corpus committed 137 logs.
- **Random suites:** root seed `20261030`, sixteen eight-transaction scenarios
  per profile, G0 revision three, at 384 and 512 nodes on O0, O2 and Yul.
  Every run matched 16 scenarios and 128 prefixes per profile. No seed was
  excluded, and both budgets drew the same forms, masks and transactions,
  with the step differing in 15 of the 16 cases of each profile.
  - Storage loops (derived seed `15499106484787201766`):
    - forms `split`, `carried` and `pipelined` came 7, 5 and 4 times, and
      masks 1, 3 and 7 came 7, 3 and 6 times;
    - iteration counts 0 to 7 came 39, 44, 10, 12, 8, 6, 6 and 3 times;
    - 20 transactions reverted after loop writes;
    - the `iteration` carry occurred in 9 cases and `rollback` in 13.
  - Keccak loops (derived seed `5144080911718836980`):
    - the forms came 6, 3 and 7 times, masks 1, 3 and 7 came 2, 7 and 7
      times, and key masks 0, 1, 3 and 7 came 6, 2, 7 and 1 times;
    - iteration counts 0 to 7 came 35, 31, 15, 19, 8, 6, 5 and 9 times;
    - 224 logs were committed, and 19 transactions reverted after logged
      iterations;
    - two iterations of one transaction shared an entry in 10 cases, and a
      later transaction reread an entry an earlier committed one wrote in 16.

A random run of a profile took 102 to 149 seconds on Sonatina and 157 to 194
on Yul. There was no finding. Hosted CI has not run the profiles.

**Enum and struct values in storage.** Every other stateful program stores
Words, std pairs and std sums. User-defined `enum` and `struct` types, `match`
over values loaded from storage, field assignment and the layout that
`std.StorageGeneric` derives for them are untested, and the pinned checkout's
own end-to-end fixtures place several of its defects there (`storage-adt-*`,
`struct-*`, `specialise-sum-of-product`). The `stateful-adt-storage` profile
generates contracts whose methods write, clear, read and update one field of
enum and struct values in contract fields and behind mapping keys, across
transactions, over an original Core reference that computes the layout itself.

The layout std derives, from `std/StorageGeneric.sol`, `std/std.sol` and the
compiler's Generic derivation (`hir-ty/src/solver/derived_generic.rs`):
- A constructor's fields form a right-nested product, one field is the field
  itself and none is the unit; the constructors of an enum form a
  right-nested sum, and a single constructor is no sum.
- A product occupies its fields' slots in order. A sum occupies one tag slot
  and the larger of its first constructor and the sum of the rest, so variant
  `i` of `n` writes tag one at its `i` outer levels, tag zero at its own level
  unless it is the last, and its payload after them. Unit occupies nothing.
- A store writes exactly those slots: a payload-free variant writes its tags
  alone and leaves every payload slot as it was. A load reads the tags from
  the outermost level and the selected variant's payload.
- Contract fields take consecutive slots by these sizes; a mapping field takes
  one, and `m[k]` of a mapping at slot `b` starts at `keccak256(b ++ k)`.
- `s.f = v` on a contract struct field is a read-modify-write of the whole
  struct through a generated setter.

A probe preceded the definitions. It wrote three contracts by hand, each with
the record and enum below and the twelve methods: variants
`(ScPair, (), word, word)` with the enum at record position 1, `(word ×3, ())`
at position 0 with `uint256` Word fields, and `((), word ×2, word)` at position
2. Each ran six scenarios of up to eight transactions: overwrites in several
orders, clears over payload variants, updates of every record field, reads
after each, both keys of a pair including `2^256 - 1` and its wrap to 0,
reverts after writes, and inputs `2^256 - 1` and `2^255 + 5`. The results:
- The pinned compiler accepted module-level `struct` and `enum` declarations
  with payloads of zero to three Words or one struct, contract fields of both
  types, mappings from a Word to each, whole-value writes of constructors
  nested in a struct constructor, `match` with nested constructor patterns on
  a field and on a mapping entry, `record.f = v` of a Word field and of the
  enum field, and the write of a payload-free variant.
- It rejected a field assignment through a mapping index, `records[k].f = v`,
  with `SC0201` ("expected struct field of a contract storage variable"). So
  a mapping entry's update is an explicit read-modify-write in the source: it
  matches the entry and writes a whole record with that field replaced.
- Imported Hull on the declared-slot runner with O0 and O2 images, and the EVM
  on O0, O2 and Yul, all matched an independent Python model of the layout on
  status, output, every observed slot and the EVM's whole storage, with no
  stray slot: 141 transactions and 705 path rows.
- `export-rust-yul.py`, run under an admitted wrapper name, compiled each
  source to one creation/runtime pair. The runtime hashes with `keccak256` and
  reads no code.
- The declared-slot runner accepts at most 32 observed slots, which bounds the
  enum at four slots with two keys.
- The Core contract below passed `Program.check` for those shapes with every
  method, at 4,057 to 4,163 nodes. It ran through `TopLevelExecution.run` in
  the unchanged runtime and equalled an independent Lean slot-map model on
  eight transactions per shape, each within 100,000 fuel.

So neither Core, the shared runtime, its proofs, the Hull importer, the
declared-slot runner, a backend, `export-rust-yul.py` nor `semantic-fuzz.py`
changes. The definitions were fixed before execution:

- **Contract:** `SynthesizedAdtStorage` declares, in order, `acc: word` at
  slot 0, `choice: ScChoice` at slot 1, `record: ScRecord`, then
  `choices: mapping(word => ScChoice)` and `records: mapping(word => ScRecord)`.
  It declares the methods its transactions call, in the order below. Each
  method takes `uint256` parameters and returns one `uint256`, and every
  transaction is zero-value.
- **Type shapes:** the module declares `ScPair { a: T; b: T; }` when a variant
  carries it, `enum ScChoice { V0, ..., V<n-1> }` and
  `ScRecord { f0; f1; f2; }`.
  - `ScChoice` has two to four variants. Each variant's payload is zero to
    three `T` fields or one `ScPair`, at least one variant has no payload, and
    the enum occupies at most four slots.
  - `ScRecord` has the enum at position 0, 1 or 2 and `T` fields elsewhere.
  - `T` is `word` or `uint256`, one per case, for every Word field of the
    three types.
  - There are 121 variant lists (9, 44 and 68 of two, three and four
    variants), 363 shapes with the enum's position, and 726 with the type.
- **Layout,** computed in Lean from the shape alone:
  - the enum's size as above, the record's two more;
  - the record at slot `1 + |ScChoice|`, `choices` after the record and
    `records` after that;
  - the tag and payload slots of each variant and the record's field offsets.
- **Plan:** the shape, the declared methods, a key base `B`, whose keys are
  `B` and `B + 1` modulo `2^256`, and a step. The plan schema
  `solcore-lean.adt-storage-plan.v1` sits under `adtStoragePlan`.
- **Methods,** in declaration and dispatch order, each with `flags` first:
  - `putChoice(flags, variant, input)` writes
    `choice = ScChoice.V<variant>(...)` and
    `putChoiceAt(flags, key, variant, input)` writes `choices[key]`;
  - `clearChoice(flags, input)` and `clearChoiceAt(flags, key, input)` write
    the first payload-free variant;
  - `getChoice(flags)` and `getChoiceAt(flags, key)` match the value, one arm
    per variant with nested `ScPair` patterns;
  - `putRecord(flags, variant, input)` and `putRecordAt(flags, key, variant,
    input)` write a whole `ScRecord` whose enum field has variant `variant`;
  - `setRecord(flags, field, variant, input)` writes `record.f<field>`: a `T`
    field's new Word, or the enum field's variant `variant`;
  - `setRecordAt(flags, key, field, variant, input)` matches `records[key]` and
    writes a whole record with that field replaced;
  - `getRecord(flags)` and `getRecordAt(flags, key)` match the record, one arm
    per variant of its enum field.

  Variants and fields are compared in order in nested `if`/`else`, the last
  branch taking any other Word; canonical calldata carries only declared ones.
- **Protocol:**
  - A writing method computes `r = step(input + acc)`, writes its value and
    sets `acc = r`; its result is `r`.
  - Every written payload Word at offset `o` from the first slot of the
    written value holds `r + o·K`, with the odd
    `K = 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95`.
    The written value is the enum for an enum write, and the record for a
    record write or update. Tags are 0 and 1, and an update writes only its
    field.
  - A read's result is the digest of the decoded Words by Horner's rule with
    `K`: for the enum, the variant index and its payload; for the record, its
    fields in order with the enum's index and payload in its place. It sets
    `acc` to the digest.
  - Odd flags revert with the result after the writes.
- **Original Core** (`core-adt-storage-contract-v1`, `wordOutcomeV1`):
  - It binds the mapping profile's Keccak closure, the step, a store closure
    `(base, (variant, value))` and a load closure
    `base ↦ (digest, K^(1 + width))`.
  - It then dispatches as std does, comparing the selector Word with each
    declared method in order: calldata shorter than four bytes or with no
    matching selector reverts with `0x4924aef0`, and the matched method checks
    its head (`0x08638556`) and reads its arguments.
  - The method then runs its protocol, with every slot as arithmetic over the
    declared base slots or a hashed entry. It uses no Core data types: tags
    and payloads are Words.
- **Source** (`solcore-source-adt-storage-v1`):
  - it imports `std`, `std.dispatch`, `std.Generic` and `std.StorageGeneric`,
    and `mstore`, `revert_` and the step's opcode aliases from `std.opcodes`;
  - the step renders as in the other profiles, as `sc_fn<k>` and `sc_step`;
  - each method converts its parameters with `Typedef.rep`, computes the
    step, and branches on the variant and field;
  - its values are constructor applications of `sc_r` plus literal offsets,
    wrapped in `uint256(...)` when `T` is `uint256`;
  - it ends with `acc = result`, the odd-flags `mstore(0, result)` and
    `revert_(0, 32)`, and `return uint256(result)`.
- **Bounds and node budget:**
  - one to eight transactions, and a default budget of 384 nodes, at most 512;
  - the 52-node shell lies inside the budget, and the 2,654-node Keccak
    closure, the enum closures (59 to 255 nodes) and the methods (at most
    1,008) lie outside it;
  - contracts are bounded by 512 + 2,654 + 1,263 = 4,429 nodes.
- **Transactions:** `{id, method, flags, key, field, variant, input, calldata,
  value}`, where only the method's own parameters appear. They are drawn in
  blocks of three from the scenario seed. Each draws:
  - its method uniformly from the twelve;
  - a variant below the variant count, a field below three and one of the two
    keys;
  - an input from the boundary bank;
  - flags from that bank with the parity of one of the four completion
    patterns of the Keccak-loop profile.
- **Generation:** each of the following comes from a SplitMix64 hash of the
  seed in its own domain:
  - the variant count, uniform in 2 to 4, then a variant list uniform among
    that count's lists;
  - the enum's position and `T`, each uniform;
  - the key base, from {0, 1, 3, `2^255`, `2^256 - 1`}.

  The step is G0's under the case's swarm mask, with the budget less the
  shell. The declared methods are those the transactions call.
- **Observations:**
  - status and output;
  - the observed slots: slot 0, the enum field's slots, the record's, and at
    both keys the entry slots of both mappings. They are derived from the
    layout with the independent `Solcore.Abi.V1.Keccak256`: at most 31 slots,
    stale payload slots included;
  - the whole committed storage on every path, with no nonzero undeclared slot
    on Hull and the EVM.

  The history schema is `solcore-lean.adt-storage-history.v1`.
- **Protocol check** of each returned row: an independent Python model of the
  layout predicts every observed slot from the prior row and the row's
  output. It checks a write's tags and `r + o·K` payload with `r` the output,
  a read's digest from the prior slots, `acc`, and every other slot unchanged.
- **Exclusions,** at the stage `adt-storage-profile`: the budget, the step's
  own exclusions, fuel (resource) and parity.
- **Reductions,** in order:
  - one-transaction removals;
  - the removal of each declared method that no transaction calls;
  - shape reductions:
    - removing a variant that no transaction names, keeping a payload-free
      one, with later variants renumbered;
    - narrowing a payload, `ScPair` to two Words and `k` Words to `k - 1`;
    - `uint256` to `word`;
  - the step;
  - flags to their parity bit, inputs to smaller bank values, and variant,
    field and key arguments to smaller ones.

  The strict order counts transactions, then methods, then the shape weight
  (variants, payload Words, `ScPair` payloads and `uint256`), then program
  size, then argument values.
- **Fixed corpus** (`scripts/semantic-adt-storage-corpus.json`): imported
  scenarios with steps from the storage corpus, plus generated seeds. It covers
  every shape class rather than every shape:
  - variant counts 2, 3 and 4, every payload kind, the payload-free variant
    first, between others and last, enum positions 0, 1 and 2, both types, the
    wrapping key base and every method;
  - for each variant count, every ordered pair of distinct variants written at
    one location one after the other and committed (20 pairs);
  - updates of a `T` field and of the enum field, in the record and in an
    entry;
  - a read of each read method whose value's slots keep a stale payload Word;
  - both keys of a mapping written in one scenario, for both mappings and
    across the wrap;
  - a reverted transaction of every writing method.

  These are the campaign dimensions `AdtVariantCounts`, `AdtPayloads`,
  `AdtClearPositions`, `AdtChoicePositions`, `AdtWordTypes`, `AdtMethods`,
  `AdtOverwrites`, `AdtFieldUpdates`, `AdtStaleReads`, `AdtNeighbourKeys` and
  `AdtRevertedWrites`, recorded for matched cases.
- **Golden tests:**
  - the emitted contracts of two shapes, written out by hand;
  - hand-written rows for three shapes, computed independently in Python and
    reproduced by original Core and the Lean model;
  - a changed expectation fails.
- **Out of scope:** generic and recursive types, `bytes` and `string` fields,
  arrays of enums or structs, nested mappings, contract-local types, the ABI
  encoding of enum or struct values, gas, value and malformed calldata.

**Results.** The checks before any random run:
- The golden tests passed. Both emitted contracts equal the hand-written text,
  and original Core and the slot-map model gave all 24 hand-written rows of
  the three shapes. The adapter's independent Python layout model agreed with
  the same rows, and a changed expectation failed.
- Original Core equalled the slot-map model on 12 generated scenarios of eight
  transactions under G0 revision three and 8 of three under revision one.
  - Every case and the reductions of two cases replayed.
  - Every variant count, enum position, Word type and method was drawn among
    64 cases, and the node counts were those fixed above.
  - Keys, fields, variants and methods outside the case, changed observed
    slots, the excluded shapes and methods out of order were refused.
- The corpus test replayed 26 scenarios and 75 transactions with every
  original Core history equal to the model's expected history, and its own
  coverage recomputation found all 20 overwrite pairs.
- An unfrozen O0 run of the corpus matched 26 scenarios and 75 prefixes with
  complete coverage, and three random eight-transaction cases matched 24
  prefixes.
- The gate passed on the final tree before `61aa80760`: the forbidden-term
  scan, `lake build` (10,251 jobs), 33 native tools prepared offline,
  `lake test`, the kernel check, 788 Python tests, every `Tests/scripts` check
  with the storage-rollback corpus, and the diff check.

The matrices ran on `61aa80760` with 96 digests frozen: the 33 native tools,
every `scripts/*.py` and `*.rs`, solc, Anvil, and the Rust driver and
code-image exporter. None changed during any run, and all 540 case results
record that revision with no tracked difference.
- **Fixed corpora:**
  - O0: all twenty-four stateful corpora matched, 328 scenarios and 896
    prefixes, in 3,189 seconds. The twenty-three earlier ones kept their 302
    scenarios and 821 prefixes.
  - The new corpus matched with complete coverage on O0, O2 and Yul: 26
    scenarios and 75 prefixes in 427, 291 and 410 seconds.
  - It covered every shape class and all 20 overwrite pairs. It updated both
    kinds of field in the record and in an entry, read a stale Word with each
    read method, wrote both keys of each mapping and across the wrap, and
    reverted 9 writes, at least one of every writing method.
- **Random suites:** root seed `20261033` (derived seed
  `5853803009084555399`), sixteen eight-transaction scenarios, G0 revision
  three, at 384 and 512 nodes on O0, O2 and Yul.
  - O2 matched 16 scenarios and 128 prefixes at both budgets, in 200 and 320
    seconds.
  - O0 and Yul both import the Sonatina O0 images on their Hull path. On both,
    the Hull deployment of one contract at 384 nodes and three at 512 ran out
    of the suite's default Hull fuel of 10,000,000. Each such case was
    reported `inconclusive-resource`, and the other 15 and 13 scenarios
    matched.
  - Each of those contracts deploys within 15,000,000. Rerun with
    `--core-fuel 40000000` under the same freeze, all four runs matched 16
    scenarios and 128 prefixes, in 198 and 201 seconds on O0 and 300 and 314
    on Yul.
  - Variant counts 2, 3 and 4 came 2, 10 and 4 times, enum positions 0, 1 and
    2 came 6, 5 and 5 times, and `uint256` 12 times. The key bases 0, 1, 3,
    `2^255` and `2^256 - 1` came 3, 4, 3, 4 and 2 times.
  - All twelve methods were called, and 35 transactions reverted, 22 of them
    writes of every writing method.
  - Four overwrite pairs, updates of both kinds in the record and in an
    entry, a stale read by `getRecord`, and both keys of each mapping
    occurred.
  - No seed was excluded. The three backends ran the same cases at each
    budget, and the two budgets drew the same shapes, keys, methods and
    transactions, with the step differing in all 16 cases.

There was no finding. The pinned front end's rejection of `records[k].f = v`
is a diagnostic of an unsupported form, not a defect. Hosted CI has not run
the profile.

**Enum arguments.** The returned enums exercise only std's generic encoder.
Its decoder of user-defined types as arguments is untested, and the pinned
checkout's fixtures `abi-dyn-sum`, `abi-sum-roundtrip`, `abi-batch-adt` and
`abi-input-bounds` record defects around it. The `stateful-enum-arguments`
profile sends a value of an enum of two to four constructors as a method
argument, canonically or malformed, and compares the whole outcome on all
three paths. Original Core decodes the calldata itself, without std's decoder
code.

std's decoder for `run(uint256 flags, E value)`, from `std.sol`,
`dispatch.sol`, `ABIGeneric.sol` and the compiler's derived instances
(`specialize/derived_abi.rs`):
- **Selector:** the signature uses std's structural `sigStr` of the enum's
  `Generic` representation. The constructors' field signatures are nested to
  the right in `sum(left,right)`: no fields give the empty string, two Words
  `uint256,uint256`, and a struct its fields' signature without parentheses.
  So `Nil | Single(uint256)` gives `run(uint256,sum(,uint256))`. The four
  selectors of `abi-sum-roundtrip` have this form.
- **Dispatch:** calldata shorter than four bytes or with another selector
  reaches the default fallback, which reverts with `0x4924aef0`.
- **Head:** `do_exec` requires `size >= 4 + h`, where `h`, the head of
  `(uint256, E)`, is 32 plus the enum's head. A static enum's head is its tag
  and its widest constructor's fields, a dynamic enum's one offset Word.
  Otherwise the call reverts with `0x08638556` (`ABIInputTruncated`).
- **Body start:** `abiSumReader` starts a static enum's body inline, at
  calldata position 36. A dynamic enum's offset Word `o` at 36 is relative to
  the arguments at 4. The bounded calldata reader requires `o <= size - 4`,
  and the body starts at `p = 4 + o`.
- **Tag:** 32 bytes must exist at `p`. The tag Word there is compared with
  each constructor's `keccak256("Name(fields)")` in declaration order, and no
  match calls `absurd()`, which reverts with empty data.
- **Fields,** relative to the body, each required to exist: one Word at
  `p + 32`; two Words, or a struct of two, at `p + 32` and `p + 64`. A `bytes`
  field's head Word `t` at `p + 32` is relative to the body. It must satisfy
  `t <= size - p`, the length Word `L` must exist at `p + t`, and
  `L <= size - (p + t + 32)`. std's later bound `L <= ~0 - 63` can then no
  longer fail. Every check is a comparison that cannot wrap, and every
  failure reverts with `0x08638556`.
- **Ignored:** trailing bytes, head Words that a narrower constructor does not
  read, and a `bytes` field's padding, which is neither required nor read:
  std copies the payload and zeroes its own padding.
- **Order:** the tag is compared before any field is read, so an unknown tag
  reverts with empty data even when its fields are cut.

A probe came first: eight hand-written contracts with
`run(uint256 flags, SynthesizedEnum value) returns (uint256)`. Each writes the
decoded constructor's one-based index and fields to slots and returns a step
result, under the protocol below with the stand-in step `3x + 7`.
- Four were static: `Nil | Single(uint256)`,
  `Wide(uint256, uint256) | Empty | Narrow(uint256) | Idle`,
  `Lone(uint256) | Rec(ScPair) | Pair(uint256, uint256)` with
  `struct ScPair { a: uint256; b: uint256; }`, and `Off | On`.
- Four were dynamic: `Value(uint256) | Data(bytes) | Gone`,
  `Nil | Single(uint256) | Double(uint256, uint256) | Blob(bytes)`,
  `Left(bytes) | Right(bytes) | Both(uint256, uint256)` and
  `Head(bytes) | Rec(ScPair)`.
- They sent 172 transactions in scenarios of up to eight: every constructor
  canonically, `bytes` lengths 0, 1, 31, 32, 33 and 64, odd flags, and the
  malformations listed below.

The results:
- Checked Hull export, Sonatina O0 and O2 images, and Yul through the pinned
  solc compiled every shape. The struct constructor's tag is
  `keccak256("Rec(uint256,uint256)")`.
- O0, O2 and Yul on Anvil, and imported Hull with O0 and O2 images, gave the
  same status, return data and slots: 860 path rows, each equal to an
  independent Python model of the reading above. 63 transactions returned
  and 9 reverted in the body; 16 were rejected with `0x4924aef0`, 44 with
  `0x08638556`, and 40 reverted with empty data.
- A prototype of the original Core contract below passed the full Core
  checker for all eight shapes and gave the model's 172 rows under the two
  comparison rules below.

So the profile is feasible on every path without a shared change. The
original Core contract uses the existing `wordOutcomeV1` convention and input
host requests, so `Solcore/ContractRuntime/` and its proofs, the Hull
importer, Core's semantics and every backend stay as they are. Core reverts
with one Word, so two comparison rules map its revert Word, each only when the
transaction's prescribed std outcome is that rejection. Under the selector
rule of the malformed-calldata profiles, Core's error selector Word stands for
std's four bytes. Under a new empty-revert rule, Core's Word zero stands for
empty revert data. Both are additive in the adapter, and Hull against the EVM
stays exact.

The profile's definitions were fixed before execution:
- **Contract:** `SynthesizedEnumArguments` with
  `run(uint256 flags, SynthesizedEnum value) returns (uint256)`, under the
  selector of the shape's structural signature. Every transaction is
  zero-value, and its calldata stays within one KiB.
- **Shape:** two to four constructors, named from the returned enums' bank
  without repetition. Each carries no fields, one `uint256`, two `uint256`s,
  one `ScPair` struct of two `uint256` fields, or one `memory<bytes>`. At most
  two carry `bytes`. A shape without `bytes` is static, any other dynamic.
- **Declared slots 0 to 4:** an accumulator, the decoded constructor's
  one-based index and three decoded Words.
- **Decoded Words** `(w0, w1, w2)`: `(0, 0, 0)` for no fields, `(a, 0, 0)` for
  one Word `a`, and `(a, b)` then 0 for two Words or the struct. A `bytes`
  field of length `L` gives `(L, c0, c1)`, where chunk `k` is the payload's
  zero-padded Word at `32k` when `L > 32k`, and zero otherwise.
- **Transaction:** once std accepts the calldata, the method reads
  `prior = slot 0`, computes `r = step(prior + index + w0 + w1 + w2)` and
  writes `r`, the index and `w0` to `w2` to slots 0 to 4. Odd flags then revert
  with the one Word `r`; even flags return `r`. A rejection runs no body and
  keeps the slots.
- **Source** (`solcore-source-enum-arguments-v1`):
  - it imports `std.Generic` and `std.ABIGeneric` beside `std` and
    `std.dispatch`, declares `struct ScPair` when a constructor carries it,
    then `enum SynthesizedEnum`;
  - the step is `sc_step`, rendered by the aggregate renderer;
  - the method matches the value with one arm per constructor, binding the
    struct's fields through `ScPair(a, b)`;
  - a `bytes` arm reads the length and each chunk with `mload` from
    `Typedef.rep`, a chunk only when the length exceeds its start.
- **Original Core** (`core-enum-argument-contract-v1`, entry `wordOutcomeV1`):
  one host contract that reads the calldata through `inputDataSize`,
  `inputDataByte?` and `inputDataWordBE?`.
  - It makes std's decisions above in std's order, with the selector and tags
    computed by Lean's Keccak-256.
  - A rejection reverts with its error selector as the Word, and an unknown
    tag with the Word zero.
  - A `bytes` chunk is the calldata Word masked to the payload. When a cut in
    the padding leaves that Word incomplete, it is the Word that ends at the
    last payload byte, shifted to the chunk's start.
  - The decoded value then runs the protocol once.
- **Node budget:**
  - the wrapper's fixed part, the dispatch, head check, flags and protocol,
    takes 168 nodes inside the budget, so the 384-node default leaves 216
    for the step;
  - the shape's decoder, the tag lookup and field decoders, lies outside the
    budget, as the long-bytes chunk guards do: 33 to 99 nodes for a static
    shape and 245 to 500 for a dynamic one;
  - the doubled budget is capped at 512, and a contract is bounded by 512
    nodes plus its decoder.
- **Step:** one checked aggregate step with one to three helpers, generated as
  for the other storage-family profiles. A step whose outputs agree at all
  boundary inputs is excluded.
- **Shape generation:** a stream of its own, started from the seed mixed by
  SplitMix64's finalizer, as for the returned enums. It draws, in order:
  1. the constructor count, uniformly from 2 to 4;
  2. zero `bytes` constructors with probability one half, otherwise one or
     two with probability one quarter each;
  3. each other constructor's fields, uniformly from none, one Word, two
     Words and the struct;
  4. the positions of the `bytes` constructors;
  5. the names, drawn from the bank without repetition.
- **Transactions:** `{id, flags, choice, first, second, length, malformation,
  calldata, stdRejection, value}`, one to eight per scenario, drawn in blocks
  of three from a separate mixed stream. Each block draws:
  - three flags from the boundary bank, each with the parity of one of the
    four completion patterns;
  - per transaction, a constructor `c` uniformly below `n`, two field Words
    `first` and `second` from the boundary bank, and a length `L` as for the
    returned enums, kept only by a `bytes` constructor;
  - per transaction, canonical calldata with probability one third, and
    otherwise a malformation: a kind uniformly from those that apply to the
    transaction, then one entry of its bank.

  A `bytes` payload is the first `L` bytes of `first · K` and `second · K`,
  with the bytes profile's odd `K`. Random runs generate the step with G0
  revision three.
- **Canonical encoding:** the selector and the flags, then either the static
  body or the offset 64 and the dynamic body. A body is the tag, the fields,
  zero Words up to the body's head, then a `bytes` field's length Word and
  zero-padded payload; that field's tail offset is the body's head.
- **Malformations** change the canonical encoding. Each kind lists its
  generation bank, where `p` is the body start, `L` the length and `size` the
  canonical size:
  - `short`: only the first 0 to 3 bytes;
  - `selector`: the selector xor 1, `2^31` or `2^32 - 1`;
  - `truncate`: a cut in the head, at and inside the tag, inside and after
    each field, at and inside a `bytes` length Word, at the last payload byte,
    at the padding, or before the last byte;
  - `trailing`: 1, 31, 32, 33 or 64 bytes of zeros, `0xff` or the ramp, as for
    malformed calldata;
  - `tag`: an unknown tag Word: 0, the tag plus one, the tag xor `2^255`,
    `2^256 - 1`, or the tag of the constructor's name with the fields
    `uint256,bytes`;
  - `retag`: another constructor's tag over the canonical body, which std
    then decodes as that constructor;
  - `offset` (dynamic): the head offset `size - 3`, `size - 4`, `size - 35`,
    `2^255`, `2^256 - 4`, `2^256 - 1`, 0, 16, 32 or 96;
  - `aliased` (dynamic): the offset 0 with the flags Word replaced by a
    constructor's tag, so that the body starts at the flags;
  - `unused` (a constructor narrower than the body's head): 1, `2^255` or
    `2^256 - 1` in its first unread head Word;
  - `tail` (`bytes`): the tail offset `size - p + 1`, `size - p`,
    `size - p - 31`, 0, 32, `2^255` or `2^256 - 1`;
  - `length` (`bytes`): `L + 1`, the most that fits, one more, `2^256 - 63`,
    `2^256 - 1`, `2^255`, `L - 1` or 0, but not `L` itself;
  - `padding` (`bytes` with padding): `0xff`, the ramp or one last byte, as
    for malformed bytes.

  Validity is structural: a kind only where it applies, a cut inside the
  calldata past the selector, and a retag of another constructor.
- **Prescribed outcome:** each transaction records `stdRejection`, std's
  revert data: `0x4924aef0`, `0x08638556`, `0x` for an unknown tag, or null
  when the body runs. A Lean model over the calldata bytes, `stdDecode`,
  computes it with the flags and the decoded Words, and the adapter's own
  Python model recomputes them.
- **Observations:** status, the whole return data, slots 0 to 4 and the whole
  committed storage, per prefix.
  - The return data is one Word on return and body revert, std's four bytes
    for an error selector and none for an unknown tag. The rules above compare
    Core's Word with the last two.
  - An accepted transaction must follow the protocol on its prescribed decoded
    value: the committed index and Words, and a returned Word equal to slot
    0. A rejection or body revert keeps the prior slots and the whole storage.
- **Exclusions, in order:**
  - a node budget too small for the fixed wrapper or above 512;
  - the step's own exclusions;
  - a step whose boundary outputs agree;
  - Core fuel exhaustion (resource);
  - a history that does not follow its prescribed outcomes.
- **Reductions:** each candidate is sealed and strictly smaller in
  transactions, then the shape's weight, then the malformations' weight, then
  the total length, then program size, then the field Words and flags.
  - A shape's weight sums one per constructor and its fields' weight: 0 to 4
    for none, one Word, two Words, the struct and `bytes`.
  - A malformation weighs 0 when there is none, otherwise one plus its
    position in its kind's bank, or one plus the bank's size outside it.

  The reductions, in order:
  - one-transaction removals;
  - a malformation set to none, then to each earlier entry of its bank;
  - shorter lengths: zero, then half the length;
  - a constructor that no transaction chooses, retags or aliases, dropped
    while more than two remain; the indices above it move down;
  - narrower fields: the struct to two Words, two Words to one, one Word to
    none, and `bytes` to none with its lengths zeroed. A malformation that no
    longer applies becomes none;
  - step reductions;
  - simpler transactions: the field Words to zero, then flags to their parity
    bit.
- **Fixed corpus coverage:**
  - constructor counts 2, 3 and 4, with every position decoded;
  - every payload kind decoded canonically, Word kinds in static and dynamic
    shapes, the struct in both;
  - decoded `bytes` lengths 0, 1, 31, 32, 33, 63 and 64, and two `bytes`
    constructors;
  - every malformation kind, each of the three rejections, and the accepted
    malformations: trailing bytes, an unread head Word, a cut that keeps every
    read byte, nonzero padding, a retag that decodes, an aliased body and a
    `bytes` length that runs into the padding;
  - both outcomes of a decoded value, a rejection between committed
    transactions, and both node budgets, 384 and 512;
  - one to three helpers, and the step features, templates and completion
    patterns of its steps.
- **Golden cases** come before any random run. The steps add a constant, and
  each expected row is written out as hexadecimal text, with tags and
  selectors from `cast keccak`: the status, the whole return data and slots 0
  to 4. They cover the decoder's exact acceptance and refusals: every payload
  kind in static and dynamic shapes, the seven bank lengths, every
  malformation kind with accepted and rejected entries, and the order of the
  checks. Original Core and the Lean model must each give every row.
- **Out of scope:**
  - nested, generic or recursive enums, enums in structs or arrays, and other
    field types;
  - more than two `bytes` constructors, and canonical `bytes` beyond 64 bytes;
  - value-bearing calls, calldata beyond one KiB, and other methods.

**Results.** The checks before any random run:
- The golden tests passed. Original Core, under the two comparison rules, and
  the Lean model gave all 35 written-out rows of the five shapes and the five
  raw-calldata rows of the order of std's checks, and a flipped expectation
  failed.
- Original Core equalled the Lean model on the cases test's generated
  scenarios: 40 of eight transactions under G0 revision three at 384 nodes,
  24 of three under revision one and 12 of four at 512.
  - Every case and the reductions of eight cases replayed.
  - Generation drew every constructor count, field kind, position and bank
    length, all thirteen malformation kinds and all five outcomes, and the
    node counts were those fixed above for every shape class.
- The adapter's Python model recomputed the calldata and std's decision of
  256 generated transactions, and its tests check std's decision for every
  malformation kind and both comparison rules.
- The corpus test replayed 21 scenarios and 60 transactions with every
  original Core history equal to the model's, and refused tampered entries.
- Unfrozen runs of the corpus matched 21 scenarios with complete coverage on
  O0 and on Yul.
- The gate passed on the final tree before `a785f293a`: the kernel check,
  `lake build` (10,272 jobs), 35 native tools prepared offline, `lake test`,
  781 Python tests, the sixteen `Tests/scripts` validators and the diff check.

The matrices ran on `a785f293a` with 153 digests frozen: the 35 native tools,
every script, solc, Anvil, and the Rust driver and code-image exporter. None
changed during any run, and all 502 case results record that revision with no
tracked difference.
- **Fixed corpora:**
  - O0: all twenty-six stateful corpora matched, 364 scenarios and 994
    prefixes, in 2,473 seconds. The twenty-five earlier ones kept their 343
    scenarios and 934 prefixes.
  - The new corpus matched with complete coverage on O0, O2 and Yul: 21
    scenarios and 60 prefixes, on O2 in 145 seconds and on Yul in 268.
- **Random suites:** root seed `20261035` (derived seed
  `15585258567353424381`), sixteen eight-transaction scenarios, G0 revision
  three, at 384 and 512 nodes on O0, O2 and Yul. All six runs matched 16
  scenarios and 128 prefixes, in 140 to 152 seconds on Sonatina and 195 and 251
  on Yul:
  - 59 and 56 transactions returned at the two budgets and 23 and 25 reverted
    in the body. std rejected 46 and 47: 11 and 13 with `0x4924aef0`, 20 and
    21 with `0x08638556`, and 15 and 13 with empty revert data;
  - every malformation kind came at 512 nodes and every kind but `padding` at
    384. std accepted 28 and 29 malformed transactions: retags, trailing
    bytes, unread head Words, aliased bodies and a longer `bytes` length at
    both budgets, and nonzero padding at 512;
  - every position of two, three and four constructors and every field kind
    in static and dynamic shapes was decoded at both budgets, with 12 and 13
    distinct `bytes` lengths;
  - 10 and 8 shapes were static and 6 and 8 dynamic; 2 and 4 had two `bytes`
    constructors, and 7 and 6 the struct;
  - at 384 nodes, 2 of 18 attempts were excluded for a step budget too small
    for the drawn template; at 512 none was;
  - the cases were identical on the three backends at each budget, and the 14
    seeds both budgets accepted drew the same shapes and transactions, with
    the step differing in 11.

There was no finding: no mismatch and no upstream defect. Hosted CI has not
run the profile.

Further state/ABI work, such as deeper nesting, static multi-word ABI elements
(`uint256[3]` or tuples) in calldata, `bytes` beyond 256 bytes, strings,
`bytes` return values beyond 64 bytes, returned enums, enum arguments and
enum arrays beyond the recorded shapes and other dynamic return values, or
callers beyond the three fixed senders, needs its own observation, rollback,
deployment and reduction definitions first.
Gas-sensitive equivalence, precompiles and arbitrary external accounts keep
their separate explicit scopes.

**Pinned end-to-end fixtures as a cross-path oracle.** Every generated
program has its own original Core reference, but the generators reach only the
language they were built for. The pinned checkout's 168 end-to-end fixtures
(`tests/e2e/*/main.sol`) also cover traits with constrained generic impls,
comptime, closures, derived classes and std's generic ABI decoder for derived
ADT arguments, and record upstream's own expectations. No original Core exists
for them. So `scripts/semantic-fixtures.py` compares their compiled paths with
each other and with each fixture's recorded expectation, and runs seeded
mutated inputs of the recorded calls across the paths only. Agreement here is
agreement among compiled paths; it is never reported as a Core comparison.

A probe preceded the definitions. It read the upstream harness
(`crates/test-directives`, `crates/test-utils/src/e2e.rs` and both backends'
`tests/e2e.rs`), exported every fixture on every path, and ran four fixtures'
recorded directives on all four paths. The results:
- **Directive forms.** The pinned grammar has two exclusive modes per fixture.
  - Method directives, in 96 fixtures: 617 typed `#[(arguments) -> expected]`
    comments and one `#[send(arguments)]` (`persistent-storage`). Upstream
    ABI-encodes typed values against the method's static ABI signature and
    runs each as an `eth_call` without `from`, which discards its state. It
    requires exact return bytes, any revert, or an exact revert payload. A
    send is a transaction from the standard Anvil account that must succeed;
    its output is not checked.
  - Raw scenarios, in 72 fixtures: one optional `#[scenario]` metadata line,
    one optional `#[deploy(bytes, value)]` (71 explicit), and 626
    `#[raw(calldata, value, label)]` transactions from a fixed sender, run in
    order on a fresh Osaka chain. Successful calls require exact bytes; a
    `revert` without bytes accepts any failed receipt.
- **Admission.** The existing parity manifests already pin all 168 fixtures
  by source hash, mode, contract, call count, Hull fuel and available gas,
  and the existing extractor and resolver supply exact directives.
  - The checked public driver rejects three fixtures before Hull, as recorded
    in Q008 and Q010: `storage-array` and `ufcs-array` (`SC0231`) and
    `module-local-function-evidence` (`SC0108`).
  - The other 165 export checked Hull with one deployment object holding one
    leaf runtime object, so no fixture contract creates another. All 165
    compile on Sonatina O0 and 164 on O2. All 165 give a Yul object that the
    pinned solc compiles to one creation object with one runtime sub-object
    and no link or immutable references.
  - The code-image tool panicked compiling `ignored-builtin-effects` at O2,
    with an assertion in Sonatina's `ir/src/dfg.rs`, though the upstream O2
    harness passes it. This is a new compiler crash; it went to
    `questions.md` without investigation.
- **Observations.** Lean Core reports per transaction the status (returned,
  reverted, invalid, out of fuel or a failure), return or revert bytes, logs,
  the contract's whole storage and every account's storage, balances and the
  account world. On Anvil, receipts, the call tracer and the prestate diff give
  the status, return or revert bytes, logs, every changed slot of every account
  reread at the receipt block, and balances. With a zero base fee and gas
  price, EVM balances change only by value transfers, as the Lean ledger does.
- Four fixtures, two of each mode (`00answer`, `persistent-storage`,
  `abi-dyn-sum` and `deposit`), matched their recorded expectations on all
  four paths and agreed on every compared field. The Lean runner reports no state for a failed
  transaction, so only successful steps compare state. A first version of the
  harness then agreed on all four paths for 156 recorded steps and mutants of
  four fixtures, with four mutants per step.

So nothing shared changes: no Core, runtime, proof, importer, runner, backend
or `semantic-fuzz.py` change. `export-rust-yul.py` gains an additive
`--fixture` admission, and the new script reuses the existing exporters,
extractor, resolver and `rust-hull-scenario` runner unchanged. The definitions
were fixed before execution:

- **Fixtures and directives:** the 168 fixtures pinned in
  `scripts/rust-scenario-parity.json` and `scripts/rust-method-parity.json`,
  with every recorded directive. A changed source hash, mode, contract or
  directive count stops the run.
- **Paths:**
  - `hull`: the pinned driver's checked Hull run by `rust-hull-scenario` on
    Lean Core, with the Sonatina O0 code images for code observables;
  - `sonatina-o0` and `sonatina-o2`: the code-image tool's creation image of
    the fixture's deployment object, on Anvil;
  - `yul`: the driver's Yul object for that deployment, compiled by solc
    0.8.35 (optimizer on, Osaka) through `export-rust-yul.py --fixture`, on
    Anvil.
- **Yul admission:** `--fixture ID` admits only that fixture's own contract,
  from its pinned path and source hash, with every existing check: exactly
  one checked Hull deployment object with one leaf runtime object, one solc
  object with one runtime sub-object, and no link or immutable references.
  The generated wrappers' admission is unchanged. Its checked Hull must equal
  the code images' checked Hull byte for byte.
- **Environment:** Anvil 1.5.1 with Osaka, chain id 31337, timestamp
  1,700,000,000, a 30,000,000 block gas limit, base fee zero and every
  transaction at gas price zero; one fresh chain per fixture, every backend
  from the same snapshot, so the contract address is the same.
  - Method fixtures deploy from the standard account
    `0xf39f…2266` (10,000 ether) at `0x5fbd…0aa3`. Each ordinary directive is a
    transaction from the zero address, value zero, on a snapshot that is
    reverted afterwards, as upstream's `eth_call` omits `from` and keeps no
    state. A send is a persisted transaction from the standard account. Each
    gets 30,000,000 gas.
  - Raw fixtures fund `0x1212…0012` with `0x10000000000000000000000000` wei,
    deploy at `0x822d…7a56` with the recorded bytes and value, and send each
    raw call as a persisted transaction with its recorded value, all with
    20,000,000 gas, as upstream does.
  - Lean Core receives the same callers, values, address and balances, the
    manifests' fuel (10,000,000 per transaction, 15,000,000 for `basic` and
    25,000,000 for `deposit`) and their fixed available gas of 30,000,000 for
    the nine fixtures whose calls pass `gas()` on. It does not meter gas.
- **Observations:** per deployment, recorded step and mutant:
  - the status: returned, reverted, exceptional (an EVM failure without a
    confirmed `REVERT`, Lean `invalid`), a resource limit (out of fuel, out of
    gas, time or output) or a path failure (any other Lean status, a code
    mismatch, a refused submission). `a931b4c99` later added Hull memory's
    range limit, described with the results;
  - the return or revert bytes, except a deployment's, whose code bytes are
    backend-specific; the Lean runner itself requires its deployed code to
    equal the O0 image;
  - the logs, in order, with address, topics and data;
  - after a successful step, the whole storage of every account (nonzero
    slots), and the balances of the contract and the fixture's sender.
- **Comparisons:**
  - each path's status and bytes against the recorded expectation, by
    upstream's rule: exact bytes for a typed result or `success(bytes)`, any
    failed receipt for a raw `revert`, a confirmed revert for a typed
    `revert`, exact bytes for `revert(bytes)`, and success for a send or a
    deployment expected to succeed;
  - the paths with each other on every observation above, for recorded steps
    and mutants alike. Two completed paths that differ in any field disagree.
    A path that hits a resource limit is left out, and makes a step on which
    the others agree incomplete rather than agreeing.
- **Mutation:** each recorded call, send and raw transaction, and each raw
  deployment with constructor bytes or a value, gets mutants that change
  exactly one thing, never the selector:
  - The arguments are read as 32-byte words after the selector, or from the
    start of a deployment's constructor bytes. A typed directive's words, a
    raw call's whose selector equals a standard-ABI method of the driver's ABI
    and whose recorded bytes decode canonically, and constructor bytes that
    decode against the constructor's inputs are classified by that signature
    as typed leaves, offsets, lengths and content. Other words, including
    derived ADT arguments, are unclassified.
  - A word becomes one of its class's boundary Words, never the recorded one:
    - `uint256` and `bytes32`: `0`, `1`, `2^255`, `2^256 - 1` and the
      recorded value ± 1;
    - `address`: `0`, `1`, `2^160 - 1`, `2^160` and `2^256 - 1`;
    - `bool`: `0`, `1`, `2` and `2^256 - 1`;
    - `int256`: `0`, `1`, `2^256 - 1`, `2^255 - 1` and `2^255`;
    - narrower integers: `0`, the range ends and the first Words outside
      it, and `2^256 - 1` for unsigned ones;
    - fixed bytes: `0`, all ones, the recorded value with dirty padding, and
      the recorded value right-aligned;
    - an offset: `0`, the recorded offset ± 32 and + 1, the input length and
      the input length less 31, `2^64`, `2^256 - 32` and `2^256 - 1`;
    - a length: `0`, the recorded length ± 1, `2^32`, `2^64` and `2^256 - 1`;
    - content: `0`, `2^256 - 1` and the recorded word with its lowest bit
      flipped;
    - an unclassified word: `0`, `1`, `32`, the recorded value ± 1, `2^64`,
      `2^255`, `2^256 - 32` and `2^256 - 1`.
  - Or a word becomes one seeded Word, kept inside a typed leaf's range.
  - Or the frame changes: the arguments lose their last byte or word or all
    of them, gain one zero byte or one word of `0xff`, or a raw call, send or
    deployment toggles its value between zero and one wei.
  - A SplitMix64 stream from the root seed, the fixture id and the step index
    orders the families (each word class, seeded Words and the frame) and
    draws one candidate per family in turn, up to 4 mutants per step.
  - A mutant runs right before its recorded step, against the state the
    recorded steps before it left, with the same sender and value, as a
    transaction whose changes are then discarded; a deployment mutant is its
    own fresh deployment. Mutants are compared across the paths only.
- **Exclusions,** each recorded with its stage and reason: an unsupported
  directive (extraction or resolution refused), a compile failure (the checked
  source rejected, or code-image, Yul or solc compilation refused), an export
  refusal (the Yul object checks) or a resource limit. Hull needs the O0
  images and every path the checked source. A compiler crash excludes its
  path and is a finding.
- **Findings:** a path mismatch, a path's expectation mismatch on a recorded
  step, a path failure, or a compiler crash. A harness error fails the run
  without becoming a finding.
- **Reduction:** each distinct finding of a fixture is rerun from a fresh
  deployment on every admitted path. It keeps only the recorded steps that
  persist state before it, then drops each of those, last first, while the
  same finding recurs. A mutated word or length then moves toward the recorded
  one: the nearest power-of-two distance that keeps the finding, then
  bisection inside it. Each reduction has 48 runs and 900 seconds.
- **Runs:** a fixed run of every admitted fixture's recorded steps on all four
  paths, then a seeded mutation run with root seed `20261111`, both with the
  scripts, the native tools, the driver, the code-image tool, the directive
  tools, solc, Anvil and cast frozen. The mutation run may reuse exports
  that the fixed run's frozen tools produced.
- **Out of scope:** code bytes and what derives from them, gas, transient
  storage across transactions, balances of other accounts, and fixtures the
  checked driver rejects. Joining the suite or the fuzz driver is later work.

**Results.** The checks before any run:
- The 21 harness tests passed. They cover:
  - the inventory and the reference SplitMix64 stream;
  - the classification of leaves, offsets, lengths and content, and each
    class's boundary Words;
  - seeded sampling and single-change application;
  - Lean and EVM observation normalization, agreement, upstream's
    expectation rule and the findings;
  - the Lean result order, the per-entry and resumed Lean invocations under
    a stalling and a buffering runner, the reduction toward the recorded word,
    and the totals.
- The 19 exporter tests passed, among them the fixture admission with every
  object, link and immutable check.
- Unfrozen smoke runs with four mutants per step on fifteen fixtures agreed
  on every step that all paths completed. They recorded the O2 crash, an
  excluded source and the `concat` path failure below as defined.
- The gate passed on the tree before `9bfedda7d`: no Lean change,
  `lake build` (10,265 jobs), 34 native tools prepared offline, `lake test`,
  the kernel check, 823 Python tests, every `Tests/scripts` check with the
  storage-rollback corpus, and the diff check. After the time-limit change,
  826 Python tests and the diff check passed again before `8bc684c78`.

A first mutation attempt on `9bfedda7d` gave each fixture one Lean invocation
for all its entries. It was stopped after 79 fixtures and 2,371 seconds:
- Lean Core meters fuel, not gas. A mutant that drives a recursion or loop
  bound to a huge Word ran for half an hour of CPU before its fuel ran out.
  The EVM paths stopped at once, out of gas or at the 1,024-item operand
  stack limit (`Out of stack`).
- `closure-parameters` took 2,068 seconds for one such mutant, and three
  other fixtures were still running.

`8bc684c78` bounds the Hull path per entry; no definition changes, as a time
limit is one of the resource limits above:
- A method fixture's deployment runs alone, then each method entry in its own
  invocation after the sends before it, within 120 seconds. Those entries
  keep no state.
- A raw scenario runs in one invocation within 600 seconds. After a limit it
  resumes past the rows reported so far, replaying the persisting steps that
  returned. If no row arrived, the first entry runs alone.

Both runs then ran on `8bc684c78` with 102 digests frozen: the 34 native
tools, every `scripts/*.py` and `*.rs`, solc, Anvil, cast, the Rust driver,
the code-image exporter and both directive tools. None changed, and the
harness's own record of every script and binary was unchanged at the end of
each run.
- **Fixed run** (584 seconds, four jobs, fresh exports):
  - Of 168 fixtures, 165 were admitted on Hull, O0 and Yul, and 164 on O2.
  - All 1,382 recorded steps agreed on every admitted path in status,
    bytes, logs, whole storage and balances. They are 165 deployments, 604
    raw transactions, 612 typed directives and one send; 1,280 returned and
    102 reverted.
  - Every admitted path matched every recorded expectation: 1,382 steps on
    Hull, O0 and Yul, and 1,377 on O2.
  - Excluded: the three rejected sources on every path, at
    `rust-checked-source` (compile failure), and `ignored-builtin-effects` on
    O2 (compiler crash).
  - The same run on `9bfedda7d` gave the same results in 644 seconds.
- **Mutation run** (root seed `20261111`, four mutants per step, 4,028
  seconds, reusing the fixed run's exports):
  - There were 4,308 mutants in 164 fixtures: 2,122 of method entries and
    2,186 of raw ones, including 18 deployments of five fixtures. The one
    admitted fixture without mutants, `storage-adt-recursive-ok`, has only a
    plain deployment.
  - The operators: 1,292 boundary Words, 828 seeded Words, 615 added zero
    bytes, 614 added words of `0xff`, 402 truncations, 339 value toggles and
    218 dropped argument lists.
  - The classified words: 1,472 `uint256`, 184 `bool`, 44 `bytes32`, 40
    `address` and 10 `bytes4` leaves, 97 offsets, 79 lengths, 76 content
    words and 118 unclassified words. A signature classified 1,156 steps.
    Among the rest, 39 raw calls had no standard-ABI method (derived ADT
    arguments), 17 recorded inputs were not canonical encodings, and 10 had
    no selector.
  - All 1,382 recorded steps again agreed and matched their expectations on
    every admitted path.
  - 4,161 mutants agreed on every admitted path: 2,563 returned and 1,598
    reverted, 658 of them with nonzero storage. None disagreed.
  - 147 mutants in 18 fixtures hit a resource limit on at least one path:
    - 116 were observed by no path. Lean Core's 120-second limit (67) or its
      fuel (45) met the EVM's gas limit on loop and recursion bounds, lengths
      and allocations of huge Words. In the other four, Hull memory's range
      limit met the EVM's gas limit; the run reported them as the path
      failures below.
    - 31 were incomplete; the paths that completed agreed. Lean Core timed out
      in each. In 10 deep recursions every EVM path halted at the operand
      stack limit (`Out of stack`). In 21, in three loop fixtures, the EVM
      paths differed in gas: Sonatina O0 and O2 returned within 30,000,000
      gas where Yul ran out (17), or only O2 returned (4). Gas is out of
      scope.

The run reported two findings; the first turned out to be a resource limit:
- In `concat` (`empty_area`, two mutants) and `zeroize-memory-range`
  (`exactRange`, two), Lean Core reported `language-failure`
  (`Solcore.Core.Value.word 6`) for a length of `2^256 - 1`. Every EVM path ran
  out of gas there, and other huge lengths ran Lean Core out of fuel. Each
  reduction kept no earlier step and found no smaller failing length within 48
  runs.
  - Word 6 is `Memory.overflowReason`: Hull memory's `touch` fails, before
    changing memory or its size, for a nonzero-length range that ends beyond
    `2^256 - 32`. No EVM transaction can pay the memory-expansion gas of such
    a range, so every EVM path can only run out of gas at the same access.
    This is a resource boundary of the Hull model, not a semantic difference
    or an upstream defect.
  - `a931b4c99` classifies such a failure as the Hull path's resource limit
    `memory-range` when every EVM path stopped at a resource limit on the
    same entry. If any EVM path returned, reverted or halted for another
    reason, that path did not reach the access, so the failure stays a path
    failure finding. Each fixture record and the totals now also count every
    path's statuses.
  - Rerun on `a931b4c99` with root seed `20261111` (33 seconds), with 103
    digests frozen (the 35 native tools, the scripts and the external tools),
    the two fixtures drew the same 104 mutants and gave the same
    observations. The only change is that those four Hull observations are now
    `memory-range`. There was no finding. 113 entries agreed, and 19 were
    observed by no path: Hull's memory range (4) or fuel (15) against the
    EVM's gas.
- Sonatina O2 crashed on `ignored-builtin-effects`, as in the probe. It went
  to `questions.md` without investigation.

No compiled path disagreed with another, on any recorded step or mutant. This is agreement among compiled
paths and with upstream's recorded expectations; no original Core reference
exists for these fixtures. Hosted CI has not run the harness, which needs the
pinned tools and Anvil.

**Mixed sequence seeds for the tuple and bytes returns.** The block choices
of `stateful-tuple-returns` and `stateful-bytes-returns` came from a raw
lcg64-v1 stream started at the block seed xor a domain. Consecutive seeds then
give starts one apart, and each draw is affine in its start, so its high half
modulo a small bound moves by a near-constant residue from seed to seed. A
measurement over three windows of 64 consecutive seeds (from the suite's
derived seeds for root seed 1 and for each profile's random-suite root, and
seeds 0 to 63) found the first block losing values:
- the first transaction's flags drew only three to five of the six bank
  indices in a window, and the bytes profile's second flags only the even
  ones in one window;
- the third transaction's input repeated in 44 to 54 of 63 consecutive seeds
  and missed one or two values in three of the six windows; it feeds the step
  and slot 2, so the third transaction saw fewer inputs;
- the other first-block draws kept their values but stepped by one fixed
  residue in 17 to 31 of 63 seeds. Later blocks were unaffected: their seeds
  are the high halves of `Sequence.blockSeeds`' own stream.

The definitions, fixed before the matrices:
- **Stream:** each block's `sequenceChoices` starts at SplitMix64's finalizer
  (`GeneratorV2.mix`) of the block seed xor the profile's domain, as the enum
  profiles' streams do. The bounds, their order, the domains, the block seeds,
  the step and the tuple arity stay as they are.
- **Versions:** `stateful-tuple-returns-v1/tuple-sequence-seed-v2` and
  `stateful-bytes-returns-v1/bytes-sequence-seed-v2`; the contracts, sources,
  templates and schemas keep their versions.
- **Fixed corpora:** imported entries keep their recorded transactions. The
  generated entries keep their seeds (2, 4 and 11 at 384 nodes and 5, 7 and 8
  at 512 for tuples; 2, 4 and 9 and 6, 8 and 13 for `bytes`) and their steps,
  and their expected histories are recomputed by the source model. Coverage
  must stay complete.
- **Fuzz state:** an existing state needs `--accept-new-epoch`.

**Results.** The checks before any matrix:
- On the same three windows, every value of every first-block draw of four to
  fourteen values came in every window. The most repeats fell from 51 and 54 to
  19 and 18 of 63, and the first 16 seeds of each window kept five or six
  (tuples) and four to six (`bytes`) of the six values of each flags and input
  draw. The uniform lengths drew 37 to 46 distinct values of 65 in a window.
- Both corpora kept their seeds and complete coverage: the corpus tests
  replayed 12 scenarios and 32 transactions each with every original Core
  history equal to the model's. The six generated entries of each corpus
  changed their histories, and the `bytes` corpus returned ten distinct
  lengths, the seven bank lengths among them.
- The gate passed on `36de9fcfb`: the kernel check, `lake build` (10,277
  jobs), 35 native tools prepared offline, `lake test`, 814 Python tests, the
  corpus validators and the diff check.

The matrices ran on `36de9fcfb` with 156 digests frozen: the 35 native tools,
every script, solc, Anvil, and the Rust driver and code-image exporter. None
changed during any run, and all 168 case results record that revision with no
tracked difference.
- **Fixed corpora:** both matched 12 scenarios and 32 prefixes with complete
  coverage on O0, O2 and Yul, in 178, 149 and 224 seconds for both.
- **Random suites:** root seed `20261036`, sixteen eight-transaction
  scenarios per profile, G0 revision three, at 384 nodes on O0, O2 and Yul.
  Every run matched 16 scenarios and 128 prefixes per profile, in 219, 206 and
  315 seconds for both profiles:
  - tuples: arities 2, 3 and 4 came 4, 5 and 7 times; 97 transactions
    returned and 31 reverted;
  - `bytes`: 96 returned and 32 reverted, with 42 distinct lengths;
  - the first three transactions' inputs took five or six of the six bank
    Words over the sixteen scenarios; the sixteen seeds of `v1`'s tuple
    matrix had given the third transaction three;
  - no seed was excluded, and the cases were identical on the three backends.

There was no finding.

**Arrays of enum arguments.** `stateful-enum-arguments` decodes one enum
value at the head of the arguments. The pinned fixture `abi-batch-adt` decodes
a calldata dynamic array whose element is a nested user ADT, element by
element through std's `abiArrayGet`. The `stateful-enum-array-arguments`
profile takes such an array of a generated enum and two indices. The pinned
std's array decoder was read before any code (`std.sol`, `dispatch.sol`):
- **Signature:** `SigString` of `calldata<array<t>>` is `typeStr(t)` then
  `[]`, and a user enum's `typeStr` is its structural `sum(...)`. So
  `run(uint256 flags, E[] items, uint256 first, uint256 second)` has the
  selector of `run(uint256,S[],uint256,uint256)`, where `S` is the enum's
  signature, as for one enum argument.
- **Dispatch:** the head is the flags, the array's offset and both indices,
  128 bytes. The lazy calldata-array decoder follows the offset `o` relative to
  the arguments at 4, reads the length `L` there and runs `checkArrayHead`:
  `L <= ~0 / s` and `L s` bytes after the length Word, for the element's
  `ABIAttribs.headSize` `s`. `s` is the body head of a static enum (its tag and
  widest fields) and 32 for a dynamic one. Elements are not decoded there.
- **Element reads:** `items[i]` is `abiArrayGet`. It requires `i < L`, else
  it reverts with `ArrayOutOfBounds()`, `0x7f52b2bf`; it checks the array's
  head again, then runs the derived decoder relative to the element region
  `R`, which follows the length Word.
  - A static element's body lies inline at `R + i s`.
  - A dynamic element's offset Word at `R + 32 i` points relative to `R`, and
    the body is decoded there as for one dynamic enum argument.
  - Unread elements are never checked.
- **Checks:** every read and advance is std's bounded calldata reader, so no
  check wraps.

A probe compiled eight hand-written shapes, four static and four dynamic, two
with the struct. Its method decodes both indexed elements and writes the length
and their decoded Words. 328 transactions ran in groups of up to eight on
imported Hull with the O0 and O2 images and on O0, O2 and Yul on Anvil:
- canonical arrays of one to four elements read at every position;
- empty arrays and indices out of bounds;
- array offsets past the end, into the head and wrapping;
- lengths of zero, past the calldata, at the overflow boundary and the maximum;
- unknown, retagged and unread tags;
- element offsets past the end, into the offset table, shared by two elements
  and unread;
- a table entry that holds a constructor's tag and is aliased by another
  element's offset;
- `bytes` tails and lengths, cut padding, cut fields, dirty unread head Words
  and trailing bytes.

All 1,640 path rows were equal to each other and to an independent model of
std's decisions: 130 returned, 8 reverted in the body, 48 with `0x7f52b2bf`,
16 with `0x4924aef0`, 110 with `0x08638556` and 16 with empty data. A
prototype of the original Core contract passed the full Core checker for all
eight shapes and gave the model's 328 rows.

Feasibility needs no shared change. `Solcore/ContractRuntime/` and its proofs,
the Hull importer, Core's semantics and host requests, every backend,
`semantic-fuzz.py` and `export-rust-yul.py` stay as they are. The storage
adapter's selector rule extends to this profile with `0x7f52b2bf` beside std's
other error selectors, and the empty-revert rule extends to it unchanged.

The definitions were fixed before execution:
- **Contract:** `SynthesizedEnumArrays` with `run(uint256 flags,
  SynthesizedEnum[] items, uint256 first, uint256 second) returns (uint256)`,
  the source type `calldata<array<SynthesizedEnum>>`, the selector of the
  structural signature above, zero value, and calldata of at most 1 KiB.
- **Shape:** as for `stateful-enum-arguments`: two to four constructors named
  from the bank, each with no fields, one or two Words, the struct `ScPair` of
  two Words or `bytes`, at most two with `bytes`. The element type is static
  exactly when no constructor carries `bytes`.
- **Declared slots 0 to 9:**
  - slot 0, the step result `r`;
  - slot 1, the length `L`;
  - slots 2 to 5, the element at `first`: its one-based constructor index and
    its Words `w0, w1, w2` as for one enum argument: `(a, 0, 0)` for one Word,
    `(a, b, 0)` for two Words or the struct, and `(Lb, chunk0, chunk1)` for
    `bytes`;
  - slots 6 to 9, the element at `second`, the same way.
- **Transaction:** std checks the head and the array; the body reads
  `items.length()`, then `items[first]` and `items[second]`, each matched with
  one arm per constructor.
  - It computes `r = step(prior + L + the index and three Words of both
    elements)`, where the sum wraps, and writes the ten slots.
  - Odd decoded flags revert with `r`; even flags return `r`.
  - A rejection reverts before any write.
- **std's decisions, in order:**
  1. fewer than 4 bytes or another selector: `0x4924aef0`;
  2. fewer than `4 + 128` bytes: `0x08638556`;
  3. the array's offset `o` at 36 with `o > size - 4`: `0x08638556`;
  4. fewer than 32 bytes at `p = 4 + o`: `0x08638556`;
  5. the length `L` at `p` with `L > ~0 / s` or `L s > size - (p + 32)`:
     `0x08638556`;
  6. for `first`, then `second`, at 68 and 100, an index `i >= L`:
     `0x7f52b2bf`;
  7. a dynamic element's offset `e` at `R + 32 i`, with `R = p + 32`, when
     `e > size - R`, or fewer than 32 bytes at `R + e`: `0x08638556`;
  8. the tag at the element's body against each constructor's tag in
     declaration order, with no match: empty revert data;
  9. the fields relative to the body, as for one enum argument: a static
     element's lie inside the checked array; a dynamic element's Words must
     exist, and a `bytes` field's tail, length Word and length must fit:
     `0x08638556`.
- **Original Core** (`core-enum-array-argument-contract-v1`, entry
  `wordOutcomeV1`): one host contract that reads the calldata through
  `inputDataSize`, `inputDataByte?` and `inputDataWordBE?`.
  - It takes std's decisions above in std's order, with the selector and tags
    computed by Lean's Keccak-256 and no std code.
  - The element decoder is one Core function, applied to `first` and then to
    `second`.
  - A rejection reverts with its error selector as the Word payload, and an
    unknown tag with the Word zero.
  - One protocol completion follows both elements.
- **Node budget:**
  - The step's budget is the node budget minus 168 nodes, the reservation of
    `stateful-enum-arguments`' wrapper, so that both profiles give the step
    one budget.
  - The array wrapper takes 358 nodes for a static element type and 397 for
    a dynamic one; it lies outside the budget beyond the reservation, with the
    shape's decoder of 26 to 108 nodes static and 197 to 452 dynamic.
  - The suite's default is 384 nodes, and the doubled budget is capped at
    512.
  - Contracts are bounded by 512 plus their nodes outside the budget, at most
    1,193.
- **Step:** one checked aggregate step with one to three helpers, generated as
  for the other storage-family profiles; it must not give equal outputs at all
  boundary inputs.
- **Shape generation:** `stateful-enum-arguments`' shape draws, from this
  profile's own stream at SplitMix64's finalizer of the seed xor its domain.
- **Transactions:** `{id, flags, elements, first, second, malformation,
  calldata, stdRejection, value}`, one to eight per scenario in blocks of
  three. Each block draws from a stream that starts at SplitMix64's finalizer
  of the block seed xor its domain:
  - three flags from the boundary bank, each with the parity of one of the
    four completion patterns;
  - per transaction an element count from 0 to 3;
  - per element `{choice, a, b, length}`: a constructor, two bank Words and a
    `bytes` length from the length bank 0, 1, 31, 32, 33, 63 and 64 with
    probability one half, otherwise uniformly from 0 to 64; only a `bytes`
    element keeps its length, and its payload is the first `length` bytes of
    `a·K ‖ b·K`;
  - `first` and `second`: each a position below the count, uniformly, with
    probability 7/8, otherwise out of bounds, the count or `2^256 - 1` with
    equal probability; with no element always out of bounds;
  - canonical with probability one third; otherwise a target element, then a
    kind uniformly from those that apply, then an entry of its bank.

  Random runs generate the step with G0 revision three.
- **Canonical encoding:** the selector, the flags, the offset 128, `first`,
  `second`, the length, then the elements:
  - a static array's bodies inline;
  - a dynamic array's offset table of one Word per element, relative to the
    region, then the bodies in order.

  A body is the tag, the fields zero-padded to the body head, then a `bytes`
  field's length Word and zero-padded payload behind its tail offset, the body
  head.
- **Malformations,** each structurally valid where it applies, and their
  generation banks, for a canonical size `n` and target element `k` with body
  start `b`:
  - `short` (0 to 3 bytes), `selector` (masks `1`, `2^31` and `2^32 - 1`) and
    `trailing` (as for the malformed-calldata profiles);
  - `truncate`: cuts at 4, 36, 68, 100, 131, 132, 163 and 164, after each
    element's tag, and at `n - 1`;
  - `offset`, the array's offset: `n - 3`, `n - 4`, `n - 35`, `2^255`,
    `2^256 - 4`, 0, 32, 64 and 96;
  - `count`, the length Word: the count plus and minus one, 0, the first
    length that does not fit, `⌊(2^256 - 1) / s⌋ + 1` and `2^256 - 1`;
  - `tag`, element `k`'s tag: 0, the tag plus one, the tag xor `2^255` and
    `2^256 - 1`;
  - `retag`, element `k`'s tag: each other constructor's;
  - `entry`, element `k`'s table Word of a dynamic array: `n - R + 1`,
    `n - R`, `2^256 - 32`, 0 and 32;
  - `share`, element `k`'s table Word: each other element's offset;
  - `unused`, element `k`'s first head Word that a narrower constructor leaves
    unread: 1 and `2^256 - 1`;
  - `tail`, element `k`'s `bytes` tail offset: `n - b + 1`, 0, 32 and
    `2^256 - 1`;
  - `length`, its `bytes` length Word: the length plus one, the longest that
    fits, one more, `2^256 - 1`, the length minus one and 0;
  - `padding`, its nonzero padding: three patterns.
- **Prescribed outcome:** each transaction records `stdRejection`:
  `0x4924aef0`, `0x08638556`, `0x7f52b2bf`, `0x` or null. It comes from a Lean
  byte-level model of std's decoder, and the adapter recomputes it with its
  own Python model.
- **Observations:** status, the whole return or revert data, slots 0 to 9 and
  the whole committed storage, per prefix.
  - The selector rule maps original Core's selector Word to std's four bytes,
    and the empty-revert rule its Word zero to `0x`; each applies only when the
    transaction's `stdRejection` prescribes it.
  - Hull against the EVM stays exact.
  - A returned row must hold the length and both decoded elements in slots 1
    to 9, and return the committed slot 0.
- **Exclusions, in order:** a node budget too small for the reservation or
  above 512; the step's own exclusions; a step whose boundary outputs agree;
  Core fuel exhaustion (resource); a history that does not follow its
  prescribed outcomes.
- **Reductions,** each sealed and strictly smaller in transactions, then
  elements, the shape, the malformations' bank positions, lengths, program
  size and the Words, indices and flags:
  - one-transaction removals;
  - simpler malformations: none, or an earlier entry of the bank;
  - the last element dropped;
  - shorter `bytes` lengths;
  - unused constructors dropped, the indices above them moving down;
  - narrower fields: the struct to two Words, two Words to one, one to none,
    and `bytes` to none;
  - step reductions, zero element Words and the flags' parity bit.
- **Fixed corpus:** imported entries over `stateful-enum-arguments`' imported
  steps, and generated seeds at both budgets. It must cover:
  - element counts 0 to 3, and both indices reading every position;
  - every field kind, static and dynamic, decoded;
  - `bytes` lengths 0, 1, 31, 32, 33 and 64, and one and two `bytes`
    constructors;
  - every malformation kind, all five rejections and acceptance, and
    malformations std accepted;
  - carries into a decoded element from an earlier committed, reverted and
    rejected transaction;
  - both node budgets.
- **Golden cases:** rows for five shapes, written out as hexadecimal text that
  the probe's independent model computes outside Lean. They include the order
  of std's checks, empty arrays, both bounds, offsets into the head and the
  table, a table entry aliased by another element, shared bodies and unread
  malformed elements. Core under both rules and the Lean model must give them
  exactly.

Out of scope: nested arrays of enums, enums with array fields, more than two
reads per call, arrays beyond three elements, calldata beyond 1 KiB,
value-bearing calls and other methods.

**Results.** The checks before any matrix:
- The golden tests passed. Original Core, under the two comparison rules, and
  the Lean model gave all 37 written-out rows of the five shapes and the six
  raw-calldata rows, among them an aliased table entry and the order of std's
  checks, and a flipped expectation failed.
- Original Core equalled the Lean model on the cases test's generated
  scenarios: 40 of eight transactions under G0 revision three at 384 nodes,
  24 of three under revision one and 12 of four at 512.
  - Every case and the reductions of eight cases replayed.
  - Generation drew every constructor count, field kind, element count, read
    position, bank length, all fifteen malformation kinds and all six
    outcomes, and the node counts were those fixed above for every shape
    class.
- The adapter's Python model recomputed the calldata and std's decision of
  all 648 transactions of 96 generated cases, and its tests check std's
  decision for every malformation kind and the order of its checks.
- The corpus test replayed 17 scenarios and 48 transactions with every
  original Core history equal to the model's, and refused tampered entries.
- A first commit of the profile emitted a step call with two extra
  parentheses, which no Lean test parses. An unfrozen smoke run showed every
  corpus source rejected; the commit was amended before any matrix, and the
  smoke runs then matched 17 scenarios with complete coverage on O0, O2 and
  Yul.
- The gate passed on `049b9c875`: the kernel check, `lake build` (10,284
  jobs), 36 native tools prepared offline, `lake test`, 821 Python tests, the
  corpus validators and the diff check.

The matrices ran on `049b9c875` with 158 digests frozen: the 36 native tools,
every script, solc, Anvil, and the Rust driver and code-image exporter. None
changed during any run, and all 511 case results record that revision with no
tracked difference.
- **Fixed corpora:**
  - O0: all twenty-seven stateful corpora matched, 381 scenarios and 1,042
    prefixes, in 2,595 seconds. The twenty-six earlier ones kept their 364
    scenarios and 994 prefixes.
  - The new corpus matched with complete coverage on O0, O2 and Yul: 17
    scenarios and 48 prefixes, on O2 in 145 seconds and on Yul in 220.
- **Random suites:** root seed `20261037` (derived seed
  `840500722863701625`), sixteen eight-transaction scenarios, G0 revision
  three, at 384 and 512 nodes on O0, O2 and Yul. All six runs matched 16
  scenarios and 128 prefixes, in 155 to 166 seconds on Sonatina and 228 and 236
  on Yul:
  - 26 and 28 transactions returned at the two budgets and 10 and 11 reverted
    in the body. std rejected 92 and 89: 36 and 37 with `0x7f52b2bf`, 33 and
    28 with `0x08638556`, 17 and 18 with `0x4924aef0` and 6 each with empty
    revert data;
  - every malformation kind but `length` came at both budgets. std accepted
    16 and 16 malformed transactions: retags, trailing bytes, unread tags, an
    unread head Word, a shared body, nonzero padding, a tail offset into the
    body and a cut of the padding;
  - every position of one, two and three elements and every field kind in
    static and dynamic arrays was read at both budgets, with 12 and 13
    distinct `bytes` lengths;
  - 9 and 8 shapes were static and 7 and 8 dynamic; 3 and 4 had two `bytes`
    constructors, and 6 and 5 the struct;
  - at 384 nodes, 1 of 17 attempts was excluded for a step budget too small
    for the drawn template; at 512 none was;
  - the cases were identical on the three backends at each budget.

There was no finding: no mismatch and no upstream defect. Hosted CI has not
run the profile.

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
