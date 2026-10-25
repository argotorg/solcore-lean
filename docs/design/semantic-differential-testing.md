# Semantic differential testing milestones

## Decision and current boundary

Prioritize a small, reproducible differential-testing campaign against
`solcore-rs`. Completing every remaining Hull correspondence proof is not a
prerequisite. Keep the existing proofs and extend them when a larger comparison
scope needs stronger evidence. This document is the implementation handoff for
that work.

The initial reference is `argotorg/solcore-rs` at
`2a745e12974c373c3799fec81b48a53c7dce2ab4`, matching the existing exporters and
fixture manifests. Pin compiler, backend, standard library and EVM versions in
every campaign. Updating the reference revision is a separate, explicit change.

The initial test domain is a closed, terminating Word/Bool fragment. It does
not observe gas, code bytes, account addresses or external state. The main
comparison must not share the Rust frontend with its reference computation.

## What already exists

| Component | Existing implementation | Boundary |
| --- | --- | --- |
| Reproducible Core generation | `Solcore/Synthesis/Core/Generator.lean`, `Seed.lean` | G0 Word/Bool expressions, local Word bindings, conditionals and primitive operations; seed, size limit and generator version are recorded. |
| Checked generated programs | `Solcore/Synthesis/Core/Fragment.lean` | `CheckedWordProgram.wellTyped` establishes typing of admitted Core programs. It does not establish correctness of a source emitter. |
| Structural shrinking | `Solcore/Synthesis/Core/Shrink.lean` | Deterministic candidates preserve the checked fragment and strictly reduce the declared complexity measure. |
| Source emission and case replay | `Solcore/Synthesis/Source/Emitter.lean`, `Cases.lean`, `Tests/SemanticCaseTool.lean` | Restricted G0 source output, explicit exclusions, versioned cases, fresh original-Core observations and checked shrink candidates. |
| Rust artifacts | `scripts/export-rust-hull.py`, `scripts/export-rust-code-image.py` | Checked Hull and exact Sonatina O0 code images from a supplied source, with revision and hash receipts. |
| Core contract execution | `Tests/RustHullScenarioRun.lean` | Deployment and ordered calls, with explicit account context and state observations. |
| Rust EVM reference | `scripts/rust-evm-reference.py` | Fixed upstream E2E fixtures on Anvil; Sonatina O0/O2 and Yul execution. |
| Compatibility inventories | `scripts/RUST_PARITY.md` | Fixed expectations checked separately by the Rust and Core paths. These are not a direct comparison runner for generated inputs. |

The restricted source emitter, operational comparison and bounded campaign are
delivered by M1 through M3. Rust's raw UTF-8 fuzz targets exercise
compiler robustness; they do not supply a typed semantic generator or
structural reducer.

## Comparison architecture

One checked G0 program produces three observations:

1. **Direct Core:** execute the original generated Core program.
2. **Rust EVM:** emit a `.sol` program, compile it through the checked Rust
   frontend and backend, and execute the resulting bytecode on the pinned EVM.
3. **Imported Hull:** import the same source's checked Rust Hull and execute it
   on Lean Core.

Direct Core versus Rust EVM is the primary comparison. Imported Hull helps
localize a difference. Agreement of both Rust-derived paths against a different
direct Core result suggests investigating the emitter or shared Rust frontend.
Agreement of direct Core and imported Hull against a different EVM result
suggests investigating the backend, EVM setup or observation adapter. These are
triage hints, not proofs of which component is wrong.

The source emitter is part of the trusted test setup until its correspondence
is proved. Do not label an unexplained difference as a confirmed upstream bug.

## Milestones

| Milestone | Deliverable | Status |
| --- | --- | --- |
| M0 | Record the scope, settle existing working-tree changes, update project documentation, and establish a tested clean baseline. | Complete, 2026-10-25 |
| M1 | Emit a checked basic G0 subset as Solcore source with a fixed contract/ABI wrapper. | Complete, 2026-10-25 |
| M2 | Execute arbitrary generated cases through the three comparison paths and save replayable results. | Complete, 2026-10-25 |
| M3 | Reduce mismatches and support bounded, repeatable campaigns suitable for CI. | Complete, 2026-10-25 |
| M4 | Add richer pure programs: multiple functions, mutation, products/sums, matches and bounded loops. | Planned |
| M5 | Add stateful scenarios: storage, ordered transactions, rollback and bounded external calls. | Planned |
| M6 | Add selected generics, closures, comptime and module combinations. | Planned |

M1 through M3 are the first operational milestone. Do not begin M4 while the
basic comparison cannot reproduce and reduce its own failures.

### M0: a clean handoff

- Keep and validate the completed parser trace proofs and the checker provenance
  correction as separate logical commits.
- Remove unfinished, redundant ledger drafts, the unrelated callable-depth
  profiling draft and the isolated identity precompile proof preparations.
  Public precompile correspondence remains deferred; executable runtime support
  is unchanged.
- Register retained proof modules in the test import graph.
- Run the full build, tests and semantic-kernel check. Finish with a clean Git
  working tree and no disposable files from this validation.
- Keep `questions.md` local and ignored. Never add it to a commit or link to it
  as required public documentation.

Completed baseline:

- `47247d25f` retains eight left-associative parser proof modules and registers
  their terminal imports in `Tests/Main.lean`. Their 37 audited public theorems
  use only the standard Lean axioms.
- `387566f24` propagates integer-pattern evidence through retained inference
  proofs. The six affected endpoints use only the standard Lean axioms.
- Five untracked drafts were removed: two superseded ledger proofs, the
  callable-depth profiling experiment, and two unconnected identity precompile
  proof preparations. No executable runtime feature was removed.
- `lake build`, `lake test`, the semantic-kernel policy check and the diff
  whitespace check passed. Validation logs and temporary proof audits were
  removed after inspection.

M0 established the baseline for source emission and operation-mapping
regressions. A Core generator alone does not complete the source-emission or
comparison milestones.

### M1: source emission

Reuse G0 generation, checking, seed provenance and shrinking. Start with Word
and Bool literals, local Word bindings, conditionals, Boolean negation, and
verified mappings for addition, subtraction, multiplication, bitwise operations
and comparisons. Use an explicit supported-operation table. Defer division,
signed arithmetic, shifts, byte extraction, exponentiation, sign extension,
count-leading-zeros and modular ternary operations until each mapping is tested.

The existing G0 generator can produce operations outside this initial subset.
Reject those inputs explicitly, or add a separately versioned generation
profile. Never silently replace an unsupported expression with another one.
Bound retries and report how many candidates were excluded. Preserve the
existing generator's replay behavior.

Emit fresh names for bindings, decimal or otherwise validated full-width Word
literals, and explicit evaluation order. Preserve conditional branch selection:
computations from an unselected branch must not be moved into unconditional
initialization. Prefer statement-based emission where needed to express a Core
`let` without changing scope. Choose source types and primitive spellings from
the pinned Rust compiler and standard library, not from the native Lean source
frontend's spelling conventions.

Use one fixed contract entry returning one ABI Word. Keep the wrapper small,
versioned and deterministic. Compare decoded return values, not constructor
bytecode or backend-generated code identities. Exercise Boolean expressions
inside the computation; a top-level Boolean ABI is unnecessary initially.

Acceptance criteria:

- A seed, node budget and generator/emitter versions reproduce identical Core
  and source artifacts.
- Every supported primitive has a hand-written mapping test, including operand
  order and 256-bit wrap behavior. Include zero, one, maximum Word and the
  signed-boundary bit pattern where applicable.
- Nested bindings, shadowing and both conditional branches have regressions.
- An emitted corpus passes the actual public Rust source checks and checked
  Hull construction. A supposedly valid generated source rejected by the
  compiler is saved as a separate finding, not silently discarded.
- Unsupported input and exhausted generation budgets have explicit results.
- State clearly that Core typing is established but emitter meaning
  preservation has not yet been formally proved.

Suggested new implementation area: `Solcore/Synthesis/Source/`, with regression
modules under `Solcore/Test/`. Inspect `Core/Wire/Host.lean` and existing Wire
runners before choosing the adapter for direct Core evaluation. Do not add a
second Core evaluator.

Delivered M1:

- `Emitter.lean` renders the supported fragment with fresh typed locals and
  branch-local computation. Unsupported operations remain explicit errors.
- `Cases.lean` and the native `semantic-case-tool` provide bounded seed search,
  original Core execution, replay validation and smaller checked candidates.
- The emitter's 15 supported and 15 rejected regression fixtures pass. Case
  regressions cover deterministic generation, explicit exhaustion, forged
  expected results, provenance/source tampering, zero fuel and checked shrinking.
- Actual checked Rust compilation and imported-Hull execution match original
  Core in 39 cases: 27 explicit operation/scope cases and twelve generated
  cases. Generation attempted 46 seeds and explicitly excluded 34 unsupported
  expressions. This validation did not execute an EVM.
- Full test-executable build (19,557 jobs), the complete test suite and the
  semantic-kernel check passed. Native command-line checks reject oversized
  inputs and zero requested counts, and report exhausted generation budgets.

See [generated semantic comparisons](../../scripts/SEMANTIC_DIFFERENTIAL.md)
for commands. Closed G0 cases may be constant-folded by Rust; source-feature
coverage must not be reported as runtime opcode coverage. Source-emitter
meaning preservation remains unproved.

### M2: direct execution comparison

Add an arbitrary-input runner; the fixed-fixture Rust E2E harness alone does not
provide this interface. Reuse the exporters and their source/tool hash checks.
Initially use Sonatina O0. Additional optimization levels and Yul are separate
comparison dimensions after the initial path works.

For every case, record:

- Original Core program, emitted source, seed, node budget and feature set.
- Generator, emitter and wrapper versions; source and artifact hashes.
- Rust, backend, standard-library and EVM revision/configuration receipts.
- ABI, constructor and call inputs, explicit execution context and budgets.
- Each path's compilation stage, execution outcome and decoded observation.
- Commands or a manifest sufficient to replay without regenerating the case.

Run checked public Rust compilation before backend execution. Some upstream E2E
entry points have different acceptance behavior; they must not silently bypass
this check. Use identical caller inputs and deployment assumptions wherever the
wrapper observes them. Reset state between independent cases.

Use separate result categories:

- Matching completed results.
- Completed semantic mismatch.
- Generated-source rejection or compilation rejection.
- Compiler crash, Core machine fault, non-resource EVM exceptional outcome, or
  adapter error.
- Inconclusive resource exhaustion: Core fuel, EVM gas, specialization budget,
  process timeout or export limit.
- Unsupported test scope.

A well-typed program is not automatically a normally returning program. Later
profiles may deliberately compare reverts and other specified failures. Never
count rejection, exhaustion, a skipped path or an absent result as agreement.
Core fuel counts machine transitions and is not EVM gas. Retry/resume policies
must be bounded and recorded; do not demand equal fuel/gas thresholds.

Acceptance criteria:

- All three enabled paths really execute each passing case and their completed
  observations agree. Keep pairwise results so a third-path mismatch cannot be
  hidden by agreement of the two primary paths.
- Deliberately perturbed observations are detected and stored as mismatches.
- Replaying a saved case restores its inputs and comparison classification.
- Resource-limit and process-failure cases cannot be reported as passes.

Delivered M2:

- `scripts/semantic-differential.py` connects fresh original-Core evaluation,
  actual checked Rust compilation, Sonatina O0 images, local Anvil deployment
  and calls, and native imported-Hull execution. A pass requires all three
  pairwise comparisons to agree.
- Saved runs include source/artifact/tool receipts. Replay verifies every
  recorded archive member and rejects tool drift before reusing the experiment.
- Valid returned bytes with the wrong ABI length remain observable mismatches.
  Missing observations, malformed transport and resource limits cannot pass.
- The runner's 22 focused regressions passed, including real subprocess limits,
  artifact tampering and classification. Actual Anvil runs covered a full-width
  Word case, nested bindings/conditions, saved-run replay, insufficient direct
  fuel and insufficient deployment gas. A modified archived code image was
  rejected before execution.

This is a single-case execution connection. Fixed feature coverage, automatic
failure reduction and bounded campaigns belong to M3. It does not establish
whole-language compiler equivalence or the source emitter's correctness.

### M3: shrinking and campaign operation

Use existing checked G0 shrink candidates, re-emit each candidate, re-check the
source and rerun the comparison. Accept a reduction only when it retains the
same failure category and relevant disagreeing paths. A source rejection must
not replace a wrong-result mismatch during reduction.

Persist the original and reduced cases, the shrink history and replay metadata.
Set limits on attempts, total runtime, artifact size and retained cases. Reuse
compiled tools and bounded batches; avoid starting a new Lean compilation for
every generated expression. Keep useful corpus cases and delete disposable
exports, temporary logs and process output after their evidence is saved.

Acceptance criteria:

- A deliberately introduced mismatch is found, reproduced and reduced.
- A fixed CI seed corpus covers every enabled operation and binding/branch
  form. Report generated, rejected, executed, matched, mismatched and
  inconclusive counts separately.
- The run has explicit time and disk limits, cleans up its child processes, and
  produces machine-readable results and a short human-readable summary.
- No performance target is claimed before measuring end-to-end throughput.

Delivered M3:

- `scripts/semantic-campaign.py` runs bounded seed searches or a fixed manifest,
  using the same three real execution paths as the single-case runner. It
  records coverage and separate outcome counts, including excluded and
  unexecuted cases. Only completed agreement contributes to passing coverage.
- The reducer rechecks and executes every accepted candidate. It preserves the
  failure category, stage, disagreeing paths and per-path outcome/payload form.
  Original and final archives remain replayable; different genuine findings
  discovered during reduction are retained separately.
- Time, disk, generation and reduction limits have explicit outcomes. Successful
  runs retain cases and compact reports while disposable exports are removed.
  SIGTERM and keyboard interruption clean up owned child processes.
- The fixed sixteen-case corpus passed all three paths and covered fifteen AST
  feature kinds and four Word boundary literals. Native corpus validation also
  checked deterministic materialization, independent feature extraction and
  fresh Core execution/replay.
- An explicit test adapter introduced a difference after actual three-way
  agreement. A nested generated case reduced to Word zero in one candidate,
  retaining its failure fingerprint. Exact replay of the reduced archive
  confirmed real agreement; replay with the adapter reproduced the synthetic
  difference. Actual observations were never modified.
- Focused regressions cover classification-preserving reduction, secondary
  findings, resource limits, manifest validation, coverage accounting and
  SIGTERM cleanup of a real child process. Zero generation attempts and an
  exhausted campaign time limit were also checked through the command line.

M1 through M3 establish the initial closed G0 testing workflow. They do not
complete the broader language profiles or the emitter's meaning-preservation
proof. Closed computations may be constant-folded; runtime-input coverage is
the next pure-program expansion before making backend opcode-coverage claims.

### M4 through M6: scope expansion

Expand one feature family at a time, including mixed-feature cases and shrink
rules. Use acyclic function calls and bounded loops before unrestricted
recursion. Stateful generation requires a model of initialized accounts and
storage, transaction sequence reduction, and comparison of committed storage,
logs, balances and relevant account lifecycle observations. Normalize
representation details while preserving observable differences.

Do not generalize pure-value success to dynamic ABI, deployment, precompiles,
gas-sensitive execution or arbitrary external contracts. Each new profile needs
an explicit supported domain and comparison rule.

## Proof priorities

Existing Hull correspondence covers finite recursive functions and loops,
language faults, concrete memory/storage/environment effects, logs, return
data, linked code observations, all four message-call modes, finite nested
children, root reentry and account destruction within the documented premises.
See [Hull meaning preservation](hull-meaning-preservation.md) for exact scope.

Precompile dispatch, creation/deployment, independent assembly semantics and
object-linking correspondence remain open. Reverse correspondence and
divergence are also outside the initial milestone. Keep these obligations
visible, but do not resume them merely to postpone M1 through M3.

If identity precompile proofs resume later, connect independent byte-copy/gas
semantics to the actual fixed runtime dispatcher and public execution. An
arbitrary-precompile-code preservation premise cannot establish correctness of
that dispatcher. Isolated helper results do not complete the public connection.

After the initial campaign works, prioritize proofs that resolve an ambiguous
comparison or support the next enabled feature. A formal source-emitter theorem
would strengthen the primary oracle. It is separate from both Core typing and
the Rust compiler's correctness.

## Planning estimates

These estimates assume one engineer familiar with the repository and working
local toolchains. They include implementation and validation, but exclude fixes
to compiler bugs discovered by the campaign. They are effort ranges, not dates.

| Scope | Estimated effort |
| --- | --- |
| Basic source emitter alone | 2–4 engineer-days |
| Working basic comparison prototype | 4–9 engineer-days total |
| M1–M3 with replay, shrinking and bounded operation | 8–15 engineer-days total |
| Through M4 | 14–27 engineer-days total |
| Through M5 | 22–42 engineer-days total |
| Selected M6 features | 34–67 engineer-days total |

For a fixed small syntax, formal generator/emitter typing, binding and parser
acceptance guarantees may require another 10–20 engineer-days. This excludes a
proof of the Rust compiler and is not an estimate for the full source language.

## Working rules and validation

Read this document, the synthesis modules, `scripts/RUST_PARITY.md`, and the
current Git status before changing the implementation. Keep this milestone
table current and record completed deliverables with their verification.

Use logical commits: settle existing proof changes, add source emission, add
execution comparison, then add reduction/campaign operation. Do not mix an
unrelated proof expansion into the differential harness. Preserve unknown local
changes until they have been inspected. Keep `questions.md` ignored for local
uncertainties; put confirmed regression cases and public limitations in tracked
tests and documentation.

Required repository checks are:

```sh
lake build
lake test
node scripts/check-kernel.mjs
git diff --check
```

Use focused Lake builds while developing and the relevant end-to-end runner
when changing an execution path. Never replace Lake artifacts manually. Delete
temporary proof checks and validation logs once their results are recorded.
