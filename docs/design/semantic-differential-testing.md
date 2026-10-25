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
| Generated storage scenarios | `Solcore/Synthesis/Core/StorageContract.lean`, `Source/StorageCases.lean`, `Stateful/StorageExecution.lean` | One checked host-aware contract, initially empty slots zero/one and one to three ordered zero-value transactions; fresh execution through `ContractRuntime`. |
| Storage comparison and replay | `scripts/semantic-storage-differential.py`, `Tests/RustHullStorageScenarioRun.lean` | Actual mined EVM transactions, original Core and imported-Hull execution; initial and per-transaction committed storage comparison. |
| Storage campaigns | `scripts/semantic-storage-campaign.py`, `scripts/semantic-storage-corpus.json` | Bounded execution, failure-preserving sequence reduction and ten fixed scenarios covering 27 transaction prefixes. |
| Rust EVM reference | `scripts/rust-evm-reference.py` | Fixed upstream E2E fixtures on Anvil; Sonatina O0/O2 and Yul execution. |
| Compatibility inventories | `scripts/RUST_PARITY.md` | Fixed expectations checked separately by the Rust and Core paths. These are not a direct comparison runner for generated inputs. |

The restricted source emitter, operational comparison and bounded campaign are
delivered by M1 through M3. Rust's raw UTF-8 fuzz targets exercise
compiler robustness; they do not supply a typed semantic generator or
structural reducer.

## Comparison architecture

Each checked case produces three observations:

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
| M4 | Add richer pure programs: multiple functions, mutation, products/sums, matches and bounded loops. | Complete, 2026-10-25 |
| M5 | Add stateful scenarios: storage, ordered transactions, rollback and bounded external calls. | In progress |
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
proof. Closed computations may be constant-folded. The M4 profiles below add
runtime inputs, while measured backend opcode coverage remains a separate task.

### M4 through M6: scope expansion

M4 begins with a separately versioned runtime Word-input profile. Its original
Core computation applies a checked Word-to-Word function to the recorded input;
the source wrapper accepts the same input through `run(uint256)`. Generation
abstracts a selected literal from a G0 body while preserving binder scope.
Admit generated functions only after direct Core execution returns distinct
results for at least two of zero, one, maximum Word and the high bit. Imported
or reduced functions may be constant. Recheck original programs, inputs,
emission and provenance on replay. Keep the existing closed G0 profile stable.

This first slice tests runtime input without claiming M4 completion or measured
opcode coverage. Initially each input is a separate comparison case; the source
function stays identical across its inputs, but compilation and deployment may
repeat. Extend this to acyclic named functions and the remaining pure feature
families listed in M4, with mixed cases and failure-preserving reduction.

The runtime-input slice is delivered:

- Checked scalar functions, scope-aware literal abstraction and checked Core
  applications have public typing results. The shared scalar renderer preserves
  the original G0 output; twelve saved G0 cases remained identical after the
  extension, including source, provenance and observations.
- Native generation, emission, replay, observation and strict reduction support
  runtime inputs. Replay validates the argument, ABI, source and generation
  filter independently of its fresh observation fuel. Generation fuel exhaustion
  has a separate classification.
- The runtime corpus contains four distinct functions at four inputs each:
  identity, input-dependent branching/scopes, and two generated functions using
  negation and multiplication. All sixteen cases matched across actual Core,
  imported Hull and EVM execution. Twelve body-feature kinds and all four
  required runtime inputs were covered; this is not opcode coverage.
- Controlled mismatch reduction retained the runtime-input profile. Exact replay
  of the reduced archive matched on all real paths, and the explicit synthetic
  adapter reproduced the same failure fingerprint. A separate eight-case
  external regression and saved-run replay also passed.
- Full repository build/tests, kernel policy, focused protocol regressions and
  both fixed corpora's deterministic native validation passed.

The acyclic named-function slice is also delivered:

- Original Core programs bind one to three Word helpers before their entry
  lambda. Scope checks admit only earlier helpers as direct callees, excluding
  recursion, escaping function values and host references. Checker admission
  supplies typing for the graph and its applied entry.
- Named source emission, versioned generation, strict replay and reduction are
  connected to all three execution paths. Reduction checks the entire graph
  and preserves helper declaration order and count. Existing G0 and runtime
  input cases retain their previous artifacts and observations.
- The fixed twenty-case corpus contains five distinct graphs: an imported
  chain, an imported diamond and generated graphs with one, two and three
  helpers, each at all four boundary inputs. All twenty cases matched across
  actual Core, imported Hull and EVM execution. Thirteen body-feature kinds,
  all four inputs and all three required declaration counts were covered.
- An additional eight-case external regression and exact replay passed.
  Controlled failure reduction preserved the function profile and helper count;
  real replay still matched, and the explicit adapter reproduced the synthetic
  fingerprint. Generation fuel exhaustion remained separately classified.
- Full build/tests, kernel policy, native validation of all three corpora and
  focused comparison/campaign tests passed. Helper declaration coverage does
  not claim dynamic call counts or backend instruction coverage.

The local-mutation slice is delivered:

- A separately versioned checked DAG admits private Word cells, direct reads
  and writes, Unit sequencing, branches and the existing acyclic Word helpers.
  Cell aliases and escaping cells are excluded. Core checking supplies typing
  of the graph and its applied entry; emitter preservation remains unproved.
- The source renderer captures each cell read in a fresh Word local before
  evaluating later effects. Unit binders stay in the indexing context even when
  they need no source declaration. Generation, replay and reduction preserve
  the full checked graph; reduction also preserves the typed binder inventory.
- All 28 fixed cases matched across actual original Core, imported Hull and
  EVM execution. Seven graphs cover read-before-write snapshots, independent
  cells, Unit branches, callee-local mutation and four generation templates,
  each at four boundary inputs. Fourteen AST features and helper counts one
  through three are covered. A separate twelve-case external regression and
  exact saved-run replay also passed.
- Controlled mismatch reduction retained the mutation profile, followed by
  matching real replay and reproduction of the synthetic fingerprint.
  Insufficient generation fuel produced an explicit resource exclusion.
- Full repository build/tests, kernel policy, deterministic native validation
  of all four fixed corpora and focused protocol/campaign tests passed.
  Template and update-count coverage is reported separately as replay-verified
  generator metadata, not as executed branch or opcode coverage.

The internal aggregate and match slice is delivered:

- A new checked profile admits Word pairs and Word sums inside functions while
  preserving the Word-only ABI/helpers and private Word cells. Nested aggregate
  types, aggregate cells and escaping cell references remain excluded. It uses
  existing Core forms; no Core primitive or evaluator change was needed.
- Pair operands retain left-to-right snapshots. Projections and match
  scrutinees execute once. Match payloads extend the Core binding context;
  generated source uses fresh pattern names and typed branch-result locals.
  Native regressions cover Word, Bool, Unit, pair and sum results from branches.
- All 32 fixed cases matched across actual original Core, imported Hull and
  EVM execution. Eight graphs cover eighteen AST feature kinds, all four
  boundary inputs, helper counts one through three, and all four generation
  templates. A separate sixteen-case external suite and exact replay passed.
- Reduction preserves both typed let binders and distinct left/right payload
  scopes. It rechecks the whole graph and requires strict decrease. Controlled
  mismatch reduction, matching real replay and synthetic replay passed, as did
  explicit generation fuel exhaustion.
- All five fixed corpora passed deterministic native validation. Thirty-two
  saved cases from the four older profiles retained exactly the same generated
  artifacts and observations. Full build/tests, kernel policy and focused
  protocol/campaign regressions passed. Feature and recipe coverage retain
  their AST/metadata scope; emitter preservation is still unproved.

The bounded-loop slice completes the restricted M4 scope:

- A checked plan retains an aggregate step DAG and a mask in zero, one, three
  or seven. The source runs a counter-based `while` for `input & mask` iterations.
  The original Core program captures the arbitrary step entry once, then checks
  finite literal ordinals against that bound and updates a private accumulator.
  No Core loop primitive or new evaluator is used.
- Every case origin, including imported and reduced cases, reconstructs and
  checks the exact original Core application from the retained plan and input.
  Replay checks source, ABI, plan, generation metadata and dependency versions.
  The source emits the arbitrary step entry as `sc_step`, rather than assuming
  it is the last declared helper.
- Generated plans use masks one, three or seven. Their steps must be input
  sensitive, and a positive-iteration input must change its value. Imported
  and reduced plans can be identity functions or have a zero mask. Reduction
  simplifies the checked step, mask or input, preserves step binders and helper
  counts, and requires a strictly smaller complete original Core program.
- All 48 fixed cases matched across the three actual paths: eight plans at
  inputs zero, one, three, seven, maximum Word and the high bit. They cover
  nineteen step AST features, helper counts one through three, all four step
  recipes, masks zero/one/three/seven and prescribed iteration counts
  zero/one/three/seven. These counts come from the validated plan; they are not
  measured runtime traces. Step coverage excludes `sc_step` and ABI wrappers.
- A separate 24-case external suite and exact replay passed, including fresh
  helper-local cells on every iteration, arbitrary entries, aggregates, zero
  iterations and Word wrap. A positive-iteration synthetic mismatch reduced
  successfully; real and synthetic replays retained their expected outcomes.
  Generation fuel exhaustion remained an explicit resource exclusion.
- Full repository build/tests and kernel policy passed. All six fixed corpora
  (160 cases) passed deterministic native generation and replay. Forty saved
  cases from the older five profiles retained identical artifacts and
  observations. Focused protocol/campaign regressions passed.

M4 is complete within the documented restrictions. M5 is in progress; M6 remains
planned. Stateful scenarios retain an original Core reference that does not
share the Rust frontend.

M5 proceeds in three connected slices:

- **M5a: committed storage and ordered transactions.** A fixed contract wrapper
  reads slots zero and one, calls a checked aggregate step with `input + old0`,
  stores its result in slot zero, increments slot one, and returns the sum of
  both reread slots. Initial storage is empty. Generated cases use three ordered
  transactions; imported/reduced cases may use one through three. The original
  host-aware Core program executes through `CheckedCoreContract` and
  `TopLevelExecution`, retaining `finalWorld` between calls. This is contract
  storage, not the private Core heap. The Rust path mines each transaction and
  obtains return bytes from that transaction's trace and storage from its
  receipt block. Compare initial state and every committed prefix, not just the
  final result. A separate Hull runner exposes the selected committed storage
  and stops on incomplete execution; an empty failed receipt world is not a
  committed-state snapshot.
- **M5b: rollback.** A separately versioned fixed protocol reverts odd original
  inputs after both storage writes and returns normally for even inputs. Both
  outcomes carry the tentative reread sum as one ABI Word. Compare completion,
  bytes and retained committed storage after every call, using the existing
  typed outcome convention and transaction checkpoints. Resource exhaustion
  must not become a revert or a passing rollback observation.
- **M5c: bounded external calls.** Add a finite account catalogue and the
  existing nested runtime. Compare parent/child outcomes and relevant committed
  storage, logs and value transfers. Record bounded call depth and scenario
  configuration, and reduce transaction sequences without changing the
  classified failure into a resource failure.

Each slice needs actual three-path comparisons, strict replay, bounded
failure-preserving reduction and a fixed corpus. M5a initially observes only
literal slots zero and one, valid `run(uint256)` calldata and zero call value.
It does not claim equivalence of arbitrary storage, gas, balances, nonce or
account lifecycle. Exact deployed Anvil addresses and caller bindings are
retained and supplied to both Core execution paths. An uncertain transaction
submission is never retried automatically. Replay always starts a fresh world.

Delivered M5a execution connection:

- `semanticStorageTool` and `rustHullStorageScenario` build the separate native
  storage tools. Generation, emission, strict case replay, observation and
  checked reduction candidates are available. Every case origin reconstructs
  the exact original host-aware Core contract from its retained aggregate step;
  no saved execution result is trusted. Reduction preserves helper/binder scope
  and surviving transaction IDs and strictly decreases the scenario measure.
- The original contract runs through the public `ContractRuntime` entry points.
  Its installed program stays fixed across the sequence, each invocation gets
  a fresh Core heap, and the terminal committed world supplies the next call.
  The separate Hull adapter exposes explicit committed slot snapshots and stops
  on incomplete execution.
- `scripts/semantic-storage-differential.py` deploys the actual linked Sonatina
  O0 images on Anvil, mines each transaction, obtains output from its trace and
  reads storage at its receipt block. All three paths receive the same actual
  caller/target bindings. Agreement is required initially and at every completed
  prefix; later resource failures preserve earlier mismatch evidence. Unknown
  submission outcomes never trigger automatic resubmission.
- Exact archive replay validates saved members, tools and budgets and repeats
  all executions in fresh worlds. The external suite passed six scenarios and
  fifteen transactions, then replayed a saved aggregate scenario. Cases cover
  storage feedback, repeated inputs, one-call sequences, sparse zero values,
  clearing/rewriting a slot, fresh private cells, arbitrary entries and aggregate
  branches. Original Core and source remain unchanged across input sequences.
- Full repository build/tests, kernel policy and 34 storage protocol regressions
  passed. The delivered profile requires successful Word returns and observes
  only slots zero and one. It does not establish emitter correctness, gas or
  ledger equivalence, or the rollback/external-call profiles.

Delivered M5a campaign operation:

- The separate stateful campaign records scenario counts and observed,
  completed and matched transaction counts. Only fully matched scenarios
  contribute to passing coverage. Time, disk, generation and shrink budgets
  remain separate, and incomplete execution cannot pass.
- The fixed ten-scenario corpus passed all 27 actual transaction prefixes. It
  covers nineteen step AST features, the six boundary inputs, one through three
  declared helpers and transactions, and all four step generator recipes.
  This is AST and scenario metadata coverage, not opcode coverage. Native
  materialization, replay and repeat observations also pass independently.
- Reduction preserves the first differing transaction's stable ID, differing
  fields and storage slots, disagreeing paths and outcome/payload forms. Case
  identity includes both the fixed program and transaction sequence. Complete
  original/final finding archives are retained; successful exports are removed.
- An explicit test adapter changed a copied slot-one observation at `tx-1`
  after actual three-way agreement. Five candidate executions accepted four
  reductions, including deleting an earlier transaction: the same finding
  remained at `tx-1`, now index zero. All actual candidate reports matched.
  Exact archive replay and fresh synthetic replay reproduced their respective
  results. Synthetic findings are kept separate from genuine discoveries.
- Twenty campaign regressions passed, including partial-history accounting,
  stable-ID failure preservation, coverage gates, budget exits and cleanup of
  owned child processes on SIGTERM.

M5a is complete within its documented scope.

Delivered M5b execution and native corpus connection:

- New `StorageRollback` Core, emitter and case modules retain the same checked
  aggregate step while fixing the odd-input completion policy. The original
  host-aware program has result type `Word + (Word + Word)` and uses
  `CheckedCoreContract.wordOutcomeV1`. The public runtime's terminal world
  supplies the next transaction; tentative writes and the revert payload remain
  distinct from committed storage. The wrapper is `SynthesizedRollback` with
  the existing `run(uint256)` selector and a separate plan/case version.
- `semanticStorageRollbackTool` supplies generation, emission, replay,
  observation and checked reduction candidates. Generated sequences use
  even/odd/even inputs and validate actual return/revert/return completion.
  Imported and reduced sequences allow other patterns. Every origin rechecks
  its exact canonical Core contract, source, transaction metadata and versions.
- The shared runner and campaign select the profile from a saved case or
  manifest. Storage execution enables Anvil step tracing so failed receipts can
  be classified by a confirmed terminal `REVERT`; resource errors take priority.
  The new profile compares 32-byte payloads and committed snapshots, including
  the requirement that a revert retain the preceding committed state. M5a
  continues to require successful Word returns.
- Eight external scenarios and 21 transactions passed all three actual paths,
  including twelve returns and nine reverts, followed by exact archive replay.
  They cover mixed and consecutive reverts, a zero payload, tentative deletion
  rollback, private cells, arbitrary entries, aggregates and zero writes.
  Changing the transaction sequence leaves original Core and source unchanged.
- The fixed twelve-scenario corpus passed native materialization, replay and
  repeated execution of all 33 transactions. It covers twenty step AST feature
  kinds, six boundary inputs, helper and transaction counts one through three,
  four generator templates, both outcomes and four ordered completion patterns.
  This validator does not execute an EVM. Full repository build/tests and kernel
  policy passed, as did forty protocol and 24 campaign regressions.

The actual fixed campaign also passed all twelve scenarios and 33 transaction
prefixes, including every required outcome and completion pattern. All ten M5a
scenarios and 27 prefixes still matched with tracing enabled. A synthetic
reverted-payload difference at `tx-1` accepted nine reductions in twelve
candidate executions, leaving only that reverting transaction. Every actual
candidate report matched; exact archive replay matched and fresh synthetic
replay retained the same stable-ID, reverted-outcome fingerprint. Exhausting
the candidate budget is reported as an attempt limit, not as proof of minimality.

M5b is complete within its documented scope. M5 remains in progress for M5c's
bounded external calls, logs and value transfers. No emitter-preservation or
broader ledger-equivalence claim follows from these results.
Usage and validation commands are in
[Generated semantic comparisons](../../scripts/SEMANTIC_DIFFERENTIAL.md#compare-ordered-storage-transactions).

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
