# Next implementation roadmap

Updated: 2026-10-26. This is the implementation order after the bounded M0–M6
milestones, not a claim that the work below has been delivered.

## Baseline

[M0–M6](semantic-differential-testing.md) provide checked generation, source
emission, three-way execution, bounded campaigns, failure-preserving reduction
and strict replay. The primary oracle executes the original generated Core;
the other paths execute Rust-produced EVM bytecode and imported Rust Hull.
Generated EVM comparisons currently use Sonatina O0. The separate upstream
fixture harness runs Sonatina O0/O2 and Yul, but that does not add those backends
to generated semantic campaigns.

Ten pure profiles and three stateful profiles are available locally. Fixed
corpora and bounded random runners exist. There is no checked-in CI workflow
or continuously scheduled campaign yet. M6d's 32 fixed cases all agreed, its
original and reduced archives replayed, and relocation of a four-file archive
was verified. The completed milestone document records the earlier evidence.

Core typing is proved for admitted programs. Source-emitter preservation,
native Source whole-compiler preservation and the remaining Hull public
connections are separate proof obligations. None follows from agreement in a
test corpus.

## Ordered priorities

| Order | Deliverable | Completion boundary |
| --- | --- | --- |
| 1 | CI and continuous bounded random campaigns across all existing profiles | Reproducible CI jobs, scheduled seed exploration, retained findings and verified cancellation/resource limits. |
| 2 | Generated Sonatina O2, then Yul comparisons | The same original cases run on each enabled backend with explicit backend provenance and replay. |
| 3 | Missing runtime operation mappings | Tested Rust-dialect mappings, dynamic-input regressions, generation, reduction and replay for each added operation. |
| 4 | Richer generated grammar | Broader typed compositions with bounded generation and reductions that preserve binding, effects and failure identity. |
| 5 | A minimal proof for the actual Rust-dialect emitter | A small connected meaning-preservation theorem for what is actually emitted, not for a substitute native Lean syntax. |
| 6 | State and ABI extensions | Explicit additional observations and transaction semantics, with actual three-way tests and sequence reduction. |
| 7 | Native Source goal two | Complete accepted-body preservation and connect all actual passes to the public session. |
| 8 | Remaining Hull public connections | Independent semantics through actual lowering, initialization and public execution for each remaining feature. |

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
6. Exercise a controlled mismatch and a resource failure through CI. Confirm
   reduction preserves the fingerprint, raw actual observations remain
   untouched by synthetic tests, and non-success outcomes produce the intended
   job result. Do not describe continuous testing as operational until the
   checked-in workflow has completed a real run.

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

## 4–8. Subsequent work

**Richer grammar:** vary typed expression and body composition beyond the
current fixed recipes. Add one family at a time, retaining alias/evaluation
order and binder-aware shrinking. Prefer finite acyclic calls and bounded
loops before unrestricted recursion. Unsupported combinations stay explicit.

**Minimal emitter proof:** begin with the actual emitted Word/Bool fragment,
fresh local bindings and conditionals. Define the relevant Rust-dialect source
meaning independently and connect the real emitter and wrapper to it. State
the parsing/typing boundary and any remaining compiler assumptions. A proof
about native Lean frontend syntax, or Core typing alone, is not this result.

**State and ABI:** expand from the existing two-slot, Word-input and bounded
call profiles to selected dynamic ABI values and richer account/storage or
transaction behaviors. Define committed observations, rollback, deployment and
sequence reduction before enabling each feature. Gas-sensitive equivalence,
precompiles and arbitrary external accounts require separate explicit scopes.

**Native Source goal two:** follow the remaining work in
[Core runtime unification](core-runtime-unification.md#remaining-work-for-the-second-goal).
Use the actual checker-derived cached-body validity, remove the restrictive
body-profile premise through general accepted-body simulation, and compose
specialization/evidence/staging/lowering with initialization and public calls.
Do not resume disconnected small lemmas in place of that public connection.

**Hull connections:** preserve the exact existing
[public theorem boundaries](hull-meaning-preservation.md). Connect precompile
dispatch, creation/deployment, independent assembly and source revert, then
object linking through real implementations and public consumers. Executable
coverage and differential agreement do not discharge these proof obligations.

## Handoff rules

Use separate commits for a coherent operational change and its validation.
Keep `questions.md` ignored and uncommitted; put confirmed regressions and
public limitations in tracked tests and documentation. Update this roadmap
when a gate is actually complete, with the commands and observed results.
Delete disposable exports and validation caches once their evidence is saved.
