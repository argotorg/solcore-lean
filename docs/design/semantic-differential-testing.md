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
| Bounded parent/child execution | `Solcore/Synthesis/Core/NestedCall.lean`, `Source/NestedCallCases.lean`, `Stateful/NestedCallExecution.lean` | Two original checked host contracts, a funded parent, one child and up to three role-based transactions; committed accounts and logs from the nested runtime. |
| Nested-call comparison | `scripts/semantic-call-differential.py`, `Tests/RustHullCallScenarioRun.lean` | Actual funded deployments and mined transactions, original Core and imported Hull; initial/per-prefix storage, balances, root payload and ordered committed logs. |
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
| M5 | Add stateful scenarios: storage, ordered transactions, rollback and bounded external calls. | Complete, 2026-10-25 |
| M6 | Add selected generics, closures, comptime and module combinations. | In progress: M6a–M6c complete |

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

M4 and M5 are complete within the documented restrictions. M6 is in progress.
Stateful scenarios retain an original Core reference that does not share the
Rust frontend.

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

M5b and M5c are complete within their documented scopes. No emitter-preservation or
broader ledger-equivalence claim follows from these results.
Usage and validation commands are in
[Generated semantic comparisons](../../scripts/SEMANTIC_DIFFERENTIAL.md#compare-ordered-storage-transactions).

M5c implementation contract:

- Install one parent and one child contract, each with initially empty slots
  zero/one. An empty payable parent constructor receives value eight; child
  deployment receives zero. Original Core starts in the resulting declared
  post-deployment world, with parent balance eight and child balance zero; it
  does not execute a corresponding source constructor. A scenario has
  one through three zero-value top-level transactions. The deployed addresses
  are distinct, valid non-precompile addresses; cases retain symbolic roles and
  bindings supply the actual addresses to every execution path.
  The Osaka boundary rejects contract addresses zero through `0x11` and
  `0x100`, including the [BLS12-381 range](https://eips.ethereum.org/EIPS/eip-2537)
  and [P256VERIFY](https://eips.ethereum.org/EIPS/eip-7951) included by the
  [Fulu/Osaka upgrade](https://eips.ethereum.org/EIPS/eip-7607).
- The parent is `SynthesizedCaller.run(uint256 target, uint256 input)`, selector
  `0x7357f5d2`. It receives the child address as the first Word and reads the
  input at byte offset 36. The payable `SynthesizedCallee` fallback receives
  exactly one raw Word at offset zero. Neither original Core program embeds a
  chosen deployment address.
- The parent adds input to its slot zero and emits topic-one/payload-new-slot
  log before calling the child. Input bit two selects value zero or one. The
  child applies the checked aggregate step to `input + oldChild0`, stores that
  result in slot zero, increments slot one and emits topic two with new slot
  zero as payload. Bit zero selects child revert; both child completions carry
  the new slot-zero Word.
- The parent stores the returned child payload in slot one, or adds one to a
  reverted payload before storing it. It emits topic three with that value and
  returns the sum of both parent slots. Bit one instead reverts with that sum.
  Unexpected call failures and non-Word returndata are exceptional exits, not
  ordinary child reverts. Source logs use the raw one-topic opcode; Core uses
  `emitLogWord(topic, payload)`. Payload bytes are big-endian Words.
- Execute original Core through `OneLevelNestedExecution.run` and carry only
  `terminal.finalWorld` into the next transaction. Compare parent outcome and
  payload, both contracts' committed slots and balances, and the ordered
  per-transaction committed logs from `terminal.committedJournal.logList`.
  Internal child outcomes are observed through their effects on the parent and
  committed state; prescribed input bits are not claimed as execution traces.
  Out-of-fuel retains the preceding committed accounts and unknown logs.
- Both linked Hull runtime images must be installed with their exact exported
  bytes. Funded EVM deployments and resulting initial balances are recorded.
  Receipt-block queries provide both committed account snapshots. Matching a
  parent revert also requires both prior snapshots and an empty committed log
  list. A child revert may retain parent writes/logs made before the call.
- Bound the sum of the actual parent and child Core node counts to 512. Fixed
  coverage includes inputs zero through seven, maximum Word and the high bit,
  so all child-revert/parent-revert/value combinations are exercised. Generation
  and reduction retain checked step scope, stable transaction IDs and exact
  canonical program reconstruction. Depth-one installed-contract calls are the
  supported domain; gas equivalence, arbitrary callees and deeper calls remain
  outside it.

Delivered M5c execution connection:

- `NestedCall` Core, emitter and case modules retain two fully checked original
  host programs and their arbitrary aggregate step. Both contracts use
  `CheckedCoreContract.wordOutcomeV1`; the fixed wrappers add 179 nodes, and
  admission measures the combined complete programs against the 512-node limit.
  Source scratch memory is reserved through the free-memory pointer, and child
  returndata must contain exactly one Word before the parent consumes it.
- `semanticCallTool` and `rustHullCallScenario` build the separate native tools.
  Generation, emission, strict replay, observation and checked reduction
  candidates are available. Plan/case schemas are `solcore-lean.call-plan.v1`
  and `solcore-lean.semantic-call-case.v1`. Transactions retain symbolic roles
  and stable IDs; `solcore-lean.call-bindings.v1` supplies the actual caller,
  parent and child addresses. Every origin reconstructs both original programs
  and the source from its checked step, without trusting saved observations.
- `scripts/semantic-call-differential.py` compares original Core, checked Hull
  and mined EVM execution. It executes the empty source deployments, including
  the parent's value-eight funding, checks linked runtime bytes and initial
  accounts, and compares every completed prefix's root status/payload, both
  contracts' storage and balances, and ordered committed logs. Receipt-block
  snapshots and transaction traces belong to actual mined transactions. Unknown
  submission outcomes never trigger resubmission. Root reverts require both
  prior snapshots and empty committed logs; resource failures remain incomplete.
- Ten external scenarios and 26 transactions passed all three paths, with
  nineteen root returns and seven root reverts. Exact archive replay of the
  aggregate scenario also passed. Inputs cover every prescribed low-three-bit
  combination, maximum Word and the high bit, with private-cell/arbitrary-entry
  and aggregate steps. Changing the input sequence preserves both original Core
  programs and source. Six additional identity sequences and fifteen
  transactions matched original Core and imported Hull.
- Full repository build (9,880 jobs), full tests and kernel policy passed, as
  did eleven protocol and thirty campaign regressions. These results establish the
  tested execution connection; they do not prove emitter preservation. Exact
  archives pin tool hashes, so a later binary or adapter update requires a fresh
  `--case` run instead of replaying an old archive under changed executables.

The separate `scripts/semantic-call-campaign.py` and fixed
`scripts/semantic-call-corpus.json` passed integration validation. The
manifest contains fourteen scenarios and 38 transactions, nineteen step AST
features, all ten boundary inputs, helper/transaction counts one through three,
and all four step recipes. Its prescribed call modes are `input & 7`; root
outcomes and ordered log patterns count only from actual completed matches.
These dimensions are distinct from dynamic opcode or internal-child trace
coverage. Native fixed-corpus validation passed all fourteen scenarios and 38
transactions across eight plans, with repeated materialization, strict replay
and repeated actual Core observations. All declared coverage and 24 negative
checks passed, including fuel exhaustion. This validator does not execute the
EVM. The actual fixed campaign also passed all fourteen scenarios and 38
transaction prefixes, with every required coverage item present. A copied log
payload difference at `tx-1` accepted three reductions in six actual candidate
executions, removing the earlier and later transactions while retaining the
same ordered-log fingerprint. Original and reduced actual reports matched;
exact archive replay matched and fresh synthetic replay retained the finding.
An actual fuel-one run remained inconclusive, preserved prior accounts and
reported unknown logs with zero completed/matched transactions. Constructor
receipts are checked against the exact linked runtime bytes for both roles;
a fresh comparison and exact replay passed after that receipt check was added.
M5 is complete within these fixed storage, rollback and depth-one call profiles.

Commands are in
[Bounded parent/child comparisons](../../scripts/SEMANTIC_DIFFERENTIAL.md#compare-bounded-parentchild-calls).

M6 proceeds in four connected slices:

- **M6a: generic selection.** Instantiate one source `select<a>` at Word,
  internal Word pair, and internal Word sum types. Evaluate the two step
  arguments eagerly in order; select using runtime input parity and consume
  the selected payload in the ABI result. The original Core reference uses a
  checked monomorphic selector and the original aggregate step graph. Keep
  the selected type during shrinking. Require both input parities for all
  three types in the fixed corpus.
- **M6b: capturing closures.** Capture runtime Word values, change the outer
  local after creation, invoke a closure more than once, and combine two
  independently created captures. Use actual Core lambdas with snapshots of
  Word values, following the pinned compiler's capture semantics. Start with
  fixed callable identities; dynamic identity selection and mutation through
  captured values are outside this slice.
- **M6c: comptime.** Evaluate a closed arithmetic expression through an actual
  source `comptime` parameter and return, then combine it with runtime input.
  The reference evaluates the original expression in Core; it must not reuse
  a Rust-computed constant as its expected answer. Reduce the checked closed
  expression and runtime step independently, then reconstruct the whole case.
- **M6d: modules and mixed features.** Emit a bounded bundle of flat source
  files with explicit imports/exports. All providers must contribute to the
  result. Exercise combinations of generic selection, captured closures and
  comptime. Save and verify every generated file, normalize generated module
  provenance by its canonical relative name, and retain separate pinned
  library provenance so exact replay works after moving an archive.

Delivered M6a:

- Sealed generic plans retain a checked aggregate step graph and one of three
  type variants. The complete monomorphic Core reference and its application
  satisfy the whole-program checker and its typing theorem. Source emits the
  genuine polymorphic selector; the runtime candidates are evaluated eagerly.
- The fixed 28-case corpus covers seven plans, nineteen step AST features,
  helper counts one through three, all four step recipes, all four Word
  boundary inputs and all six variant/parity combinations. All 28 cases pass
  actual checked Rust compilation and agree across original Core, imported
  Hull and Sonatina O0 on local Anvil.
- Native validation reconstructs every case twice, executes and replays it,
  checks twelve strictly smaller candidates across all three variants and
  rejects fifteen tampered or out-of-budget cases. Separate native checks
  covered twelve original and 48 reduced cases. Forty-eight saved cases from
  the six previous pure profiles retained byte-identical artifacts and results.
- A generated pair case with high-bit input was reduced in eight accepted
  candidate executions, retaining its type and mismatch fingerprint; its
  final input is zero. These differences were introduced only in a separate
  test analysis after actual agreement. Original and reduced archive replays
  matched, and synthetic replay reproduced the same fingerprint. The attempt
  limit was recorded; this is not a minimality claim.
- Fuel-one execution was inconclusive rather than matched. Thirty adapter and
  46 campaign regressions passed, as did the existing stateful policy suites,
  the full repository build/tests and semantic-kernel check. No upstream
  compiler bug was found in this slice.

Delivered M6b:

- Sealed closure plans capture runtime Word snapshots, retain an actual Core
  higher-order apply function, mutate the outer cell after closure creation,
  and either reuse the first closure or construct a second independent one.
  Thirty-two hand-checked Core applications cover boundary values, private
  cells, arbitrary entries and constant imported steps.
- All 24 fixed cases across six plans pass the real three-way comparison.
  Coverage includes nineteen step AST features, all four boundary inputs,
  all four aggregate recipes, one through three helpers and both capture
  variants. Native validation repeats materialization and execution, checks
  eight strictly smaller candidates and rejects fifteen tampered or bounded
  resource cases. Separate native checks covered eight originals and 32
  reductions; 56 saved cases from the seven earlier pure profiles were
  byte-identical after the extension.
- An independent-capture case reduced its step in eight accepted executions
  while retaining its maximum-Word input, capture recipe and synthetic
  mismatch fingerprint. Original and reduced actual archives replayed with
  agreement; fresh synthetic replay reproduced the same fingerprint. The
  recorded attempt limit makes no minimality claim. Actual fuel-one execution
  remained inconclusive.
- Thirty-one adapter and 51 campaign policy regressions passed. The full
  repository build (9,890 jobs), test suite and semantic-kernel check passed.
  This slice makes no claim about aggregate captures, writes through captured
  values, escaped factories or dynamically selected callable identities.

Delivered M6c:

- The complete original closed G0 constant and aggregate step ASTs remain in
  the checked Core reference. Source evaluates the constant through genuine
  comptime parameters and returns. Offset/scale variants use it with runtime
  input; the emitter never replaces it with a Rust-derived constant. Forty-eight
  Core applications and five standalone constant goldens cover branch-local
  calculations, all supported scalar operations, Word wrap and private cells.
- All 32 fixed cases across eight plans match in the real three-way campaign.
  Coverage separates 21 step AST features from all fifteen enabled constant
  AST features. Both variants, four boundary inputs, one through three helpers
  and all four step recipes are present. Native validation checks eleven
  smaller candidates and twenty negative/budget/resource cases. Separate
  native checks cover sixteen generated, eight imported and 32 reduced cases;
  64 saved cases from the eight prior profiles remain byte-identical.
- Random generation reserves at most eight nodes for the constant and records
  both original seeds and node allocations. With seed one, 384 nodes and a
  512-attempt bound, sixteen cases were generated after 273 attempts with 269
  explicit exclusions. Larger constant ASTs remain admitted for imported
  cases and are covered by the fixed corpus. This is not a throughput claim.
- A scale case reduced both its constant and step in twelve accepted real
  executions, retaining its maximum-Word input and synthetic failure
  fingerprint. Original/reduced actual archive replay and fresh synthetic
  replay passed. The recorded attempt limit does not imply minimality.
  Actual fuel-one execution remained inconclusive.
- Thirty-two adapter and 56 campaign regressions passed. The full repository
  build (9,895 jobs), test suite and semantic-kernel check passed. A runtime
  value passed to a comptime parameter was independently rejected during
  Rust's comptime evaluation with `SC0409`. No upstream bug was found in this
  slice; native Lean frontend staging remains outside this profile.

Each slice requires fresh three-way execution, strict native reconstruction,
failure-preserving reduction, a fixed corpus and saved-run replay. M6 remains
in progress until all four slices meet those requirements. None establishes
formal correctness of the source emitter or unrestricted feature coverage.

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
