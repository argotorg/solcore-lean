# Running the semantic test suite

The [workflow](../.github/workflows/semantic.yml) runs the existing differential campaigns of
[SEMANTIC_DIFFERENTIAL.md](SEMANTIC_DIFFERENTIAL.md). It does not replace their Core reference,
runtime adapters, reduction or replay rules. The
[implementation roadmap](../docs/design/next-implementation-roadmap.md) records the status and the
next priorities.

Run records up to 2026-11-17 are in git history at `049f8ce1f`.

## Tools

Install Python 3.11 or newer, Git, Rust 1.97.0 through rustup, the toolchain in `lean-toolchain`
through elan, and Anvil 1.5.1. The EVM hardfork is Osaka. For Yul comparisons also install solc
`0.8.35+commit.47b9dedd`, chosen with `--solc`; the Yul exporter checks its full version and
binary hash. The CI Yul job downloads the Linux amd64 release from the
[official binary inventory](https://binaries.soliditylang.org/linux-amd64/list.json) and verifies
the pinned SHA256 before making it executable.

```sh
python3 scripts/prepare-semantic-tools.py --plan
python3 scripts/prepare-semantic-tools.py --prepare --allow-network
python3 scripts/prepare-semantic-tools.py --verify
```

- The bootstrap verifies these versions and never installs system tools itself.
- Preparation fetches the exact pinned Rust revision into a new directory, checks its tracked
  files and fetches the locked dependencies. It builds the two exporters, the directive extractor
  and resolver and the declaration and site extractors offline, and the forty-two native Lean
  tools in one Lake invocation.
- An existing checkout with another revision or unrelated edits is rejected.
- Network access needs `--prepare --allow-network`; without `--allow-network`, preparation uses
  the existing dependency downloads. Verification is read-only and offline.
- The readiness receipt hashes the tool executables, native sources, exporter sources,
  dependency locks and build receipts. Changed inputs or binaries need fresh preparation, and no
  cache is accepted merely because its directory exists.
- The CI cache holds dependency downloads, not executable proof artifacts or saved expected
  results. CI disables Cargo incremental compilation and debug information to limit disk use.
- The stateful comparisons enumerate EVM storage from Anvil's prestate diffs. After changing
  Anvil, run `python3 scripts/check-evm-storage-diff.py`, which checks on probe contracts that
  those diffs report every changed slot.

## Fixed and random suites

```sh
python3 scripts/semantic-suite.py --mode fixed \
  --seconds 7200 --profile-seconds 900 --output .upstream/semantic-fixed
python3 scripts/semantic-suite.py --mode random --seed 20261026 \
  --cases 16 --attempts 2048 --seconds 3600 --profile-seconds 600 \
  --output .upstream/semantic-random
```

The default selection is all 66 profiles, listed in the
[profile table](SEMANTIC_DIFFERENTIAL.md#profiles). Repeat `--profile NAME` to select fewer.
Profiles run one after another.

**Fixed mode** runs all 3,517 manifest cases and scenarios. It rejects `--cases`, `--functions`,
`--nodes` and `--nodes-scale` rather than silently truncating required coverage.

**Random mode** derives each profile's starting seed from the root seed, the profile, the shard
index and count and the derivation version.
- `--shard-index` and `--shard-count` give reproducible, independent starting points; they do not
  claim disjoint generated programs. Every shard runs every selected profile.
- Generation attempts and exclusions stay in the report, and rejected source is never retried
  as if it had not been generated.
- `--nodes-scale S`, from 1 to 4, multiplies each profile's default node budget, capped at 512
  nodes or at a plan-based pure profile's limit; an explicit `--nodes` wins.
- Random campaigns of the seventeen G0-based pure profiles generate with
  [G0 revision four](SEMANTIC_DIFFERENTIAL.md#g0-generator-revisions) (`core-g0-v4/lcg64-v1`),
  and the random steps of every stateful profile with revision three (`core-g0-v3/lcg64-v1`),
  which the stateful tools require.
- The twenty-four runtime-input profiles whose functions can be identities apply the acceptance
  filter `exclude-boundary-identity-v1`
  ([boundary identities](SEMANTIC_DIFFERENTIAL.md#boundary-identities)).
- Random runtime-input cases run each function at its boundary inputs and then at four
  seed-derived inputs, and random stateful scenarios have eight transactions. Fixed corpora and
  saved cases keep the revision, inputs and sequence they record.
- Each profile row of the report lists `generatorVersions`, `inputSelections`, `acceptances` and
  `transactions` under `campaign.generation`.

**Whole functions.** `--cases` counts a function's inputs separately, so a random run of a
runtime-input profile covers one function per eight to twelve cases, and its last function may
lose inputs. `--functions N` instead gives every random runtime-input pure profile N whole
functions, while `closed-g0` and the stateful profiles keep `--cases`; the report records N in
`functions`.
- A campaign returns at most 1,024 cases, so N is at most 85 while a twelve-input profile is
  selected.
- Without `--attempts`, `--functions N` gives each of those profiles at least 16 attempts per
  function, up to 10,000.
- A generation response is limited to 2 MiB, so a larger request is split into requests of whole
  functions that continue the same seed sequence and merge to the same cases. Only a function
  whose cases alone exceed 2 MiB stops, as an inconclusive `output-limit`
  ([whole functions](SEMANTIC_DIFFERENTIAL.md#seeded-runtime-inputs)).

**Backends.** `--backend sonatina-o0` is the default, and `--backend sonatina-o2` compares the same
cases after O2 compilation. Random generation uses the same seeds on every backend, so
optimization does not change the generated inputs. The CI matrix runs each backend in its own
job with its own reports and artifacts, and a failure in one does not cancel another.

| Backend | Fixed cases or scenarios | EVM execution | Imported Hull code images |
| --- | ---: | --- | --- |
| `sonatina-o0` | 3,517 | Sonatina O0 | Sonatina O0 |
| `sonatina-o2` | 3,517 | Sonatina O2 | Sonatina O2 |
| `yul` | 2,994 pure; with `--profile`, 416 storage-family, 45 call-return, 16 call-sequence and 18 call-branch | optimized solc Yul, Osaka | Sonatina O0 |

- `--backend yul` selects the thirty-four pure profiles by default. The twenty-seven
  storage-family profiles and the call-return, call-sequence and call-branch profiles also run on
  Yul when `--profile` selects them
  ([storage family](SEMANTIC_DIFFERENTIAL.md#compare-storage-family-contracts-on-yul),
  [call returns](SEMANTIC_DIFFERENTIAL.md#compare-call-returns),
  [call sequences](SEMANTIC_DIFFERENTIAL.md#compare-call-sequences),
  [call branches](SEMANTIC_DIFFERENTIAL.md#compare-call-branches)).
- Selecting `stateful-calls` or `stateful-forwarded-value` with Yul fails before execution:
  each compiles both contracts from one source.
- A random Yul run of the default selection with `--cases 16` requests 544 cases.
- The shared preparation builds the Rust and Lean tools; solc is supplied and checked separately.
- Every backend uses the original generated Core as the primary reference. Yul's linked layout
  is not given to the Hull importer, so Yul compares only observations that do not depend on code
  layout; reports record this in `pathBackends`.

**Limits.** The suite bounds total and per-profile time and disk, subprocess output, generation,
case execution and reduction.
- Defaults: 1 GiB for the whole suite and 256 MiB for one profile.
- Hull fuel (`--core-fuel`) defaults to 40,000,000, enough to deploy the largest storage-family
  contracts from Sonatina O0 images; a run that exhausts it is inconclusive.
- The limits bound the suite's outputs, not the separately prepared toolchains and build caches.
- SIGTERM and a keyboard interrupt stop the owned processes, including compiler and Anvil
  children in separate process groups, and record the unfinished work.

**Exit status.** Only complete agreement with the required coverage exits zero. Findings, missing
results, generation exhaustion and resource exhaustion exit nonzero, and a mismatch found before
a later interruption stays a finding. Reports give per-profile elapsed time,
accepted, excluded, executed and matched counts and measured throughput; these are not runtime
opcode coverage.

**Budget.** The complete fixed suite no longer fits the CI job's 7,200 seconds on Sonatina O0, so
split the fixed job by `--profile` to keep each part within its budget
([per-case overhead](SEMANTIC_DIFFERENTIAL.md#per-case-overhead-and-the-fixed-suites-budget)). On
Yul, `runtime-memory-arrays` used 619 of its 900 `--profile-seconds`.

## Findings and replay

- Successful campaigns keep their cases and compact reports and remove disposable exports.
  Findings keep the complete original and reduced archives and their failure fingerprints.
- Replay an archive with the matching pure, storage or call runner. Exact replay needs the
  recorded tools and pinned library identities. With changed tools, start a new comparison from
  the saved case; that is not an exact replay of the earlier environment.
- A pure campaign compiles each distinct source once per backend and shares it among cases whose
  source files, backend, library, exporters and compiler builds match by digest. Every archive
  still holds its own copies of the outputs and records the shared compilation in
  `report.compilation`, and exact replay compiles again.
- A fixed pure campaign generates each corpus recipe once for all its entries' inputs and hashes
  each unchanged tool once. The nine pure profiles whose cases carry large Core references keep
  their case files as compact JSON.

The CI finding check uses a reducible fixed addition case:

```sh
python3 scripts/check-semantic-findings.py \
  --case .upstream/semantic-fixed/00-closed-g0/cases/0006.json \
  --output .upstream/semantic-findings
```

- It introduces a synthetic difference only in a separate analysis, after real agreement; the
  original runtime observations stay untouched.
- It requires an accepted reduction, exact replay of the reduced actual archive, reproduction of
  the synthetic fingerprint and an actual fuel-one run classified as inconclusive. A compiler or
  runtime failure fails the check.
- `--backend sonatina-o2` keeps that selection through reduction and exact replay, including its
  mismatch fingerprint. `--backend yul [--solc PATH]` runs the check with actual Yul compilation.
- Yul archives also keep the checked Yul, the exact solc request and response, both bytecodes and
  the matching Hull, source and tool receipts. Replay verifies these files locally, so a moved
  archive does not depend on its original source directory.

## Continuous fuzzing

`scripts/semantic-fuzz.py` runs the random suite repeatedly on one machine and keeps a registry of
what it finds. Prepare the tools first, then start it:

```sh
python3 scripts/semantic-fuzz.py run --state .upstream/semantic-fuzz \
  --base-seed 20261101 --shard-index 0 --shard-count 1
python3 scripts/semantic-fuzz.py report --state .upstream/semantic-fuzz
python3 scripts/semantic-fuzz.py label --state .upstream/semantic-fuzz SIGNATURE 'triage note'
```

**Iterations.** Iteration `i` runs the suite in random mode once per backend with root seed
`base + i`, so the backends compare the same generated programs. All three backends run by
default.
- On Yul the driver runs the pure, the twenty-seven storage-family and the call-return,
  call-sequence and call-branch profiles, whether profiles are configured or not, and never
  `stateful-calls` or `stateful-forwarded-value`. It selects the stateful ones explicitly, since
  the suite's own Yul default is the pure profiles. With the default sixteen cases this adds 480
  eight-transaction scenarios to each Yul iteration.
- Machines that share a base seed use their own `--shard-index` of a common `--shard-count`.
- The first `run` fixes the configuration in `config.json`: backends, profiles, cases (default
  16), whole functions (`--functions`, unset by default), attempts (2,048), node-budget scales,
  time and disk limits and tool paths. Later runs resume after the last recorded run and refuse
  different options; use a new state directory for another configuration.
- `--size-cycle 1,2` (the default) gives iteration `i` the scale at position `i` modulo the cycle,
  so every other iteration doubles each profile's default node budget, within the caps of
  `--nodes-scale`, and generates larger programs.
- `--iterations N` stops after N iterations. A `STOP` file in the state directory stops before the
  next run, and SIGTERM or SIGINT stops the running suite, which records its unfinished work. An
  interrupted run moves to `interrupted/` and reruns from its seed on the next start; its partial
  findings are not counted.
- `--jobs N` runs N suites at once, each on its own iteration and backend. Seeds still follow the
  iteration, so results do not depend on N. The ledger records runs as they complete, and a
  resumed driver fills gaps before new iterations. Each suite runs one compiler, one Anvil and the
  Lean tools at a time; choose N by the host's cores and memory, since an overloaded host turns
  case timeouts into inconclusive results.

**Epochs.** Before every run the driver verifies the prepared tools offline. The digests of the
readiness receipt and of the harness scripts form an epoch. When the tools or scripts change, the
driver stops until it is restarted with `--accept-new-epoch`, and the ledger records each run's
epoch.

**Ledger and registry.** Every run appends a line to `ledger.jsonl` with its seeds, statuses,
counts, finding occurrences and problems. Each occurrence is counted in `registry.json` under a
signature made of the backend, category and stage plus one of:
- for compiler crashes, rejections and other tool failures, the first panic location and message,
  or the first error line, without paths, thread identifiers or numbers. For a panic the driver
  also replays the failing Rust stage from a scratch copy of the archive with `RUST_BACKTRACE=1`
  and adds the first two frames outside the panic machinery and the panicking library, so panics
  raised at one library location by different compiler code count separately. The replay never
  revisits the run's classification, and `--no-crash-replay` turns it off;
- for semantic mismatches, the profile, the rest of the mismatch fingerprint and the reduced
  program's digest.

- The first `--examples` occurrences of a signature (default three) keep their complete archives
  under `findings/SIGNATURE/` with an `occurrence.json`. Later occurrences are counted with their
  seeds, from which random cases replay with the tools and scripts of the run's epoch.
- The ledger also records each profile's generator versions, input selections and transaction
  count, and for pure profiles the distinct sources, compilations and reused compilations.
- Runs that pass are deleted. Other runs keep their suite summary and the summaries and logs of
  the profiles that did not pass. `run --keep-runs` keeps complete run directories instead. A
  profile that did not pass without a finding, or was left unexecuted, is listed as a problem.
- `label` records a triage note for a signature in `labels.json`. A labelled signature is shown as
  known; it stays counted and listed, and its new occurrences still enter the ledger.
- `report.md` and `report.json` list the signatures (untriaged first, new ones marked), the run
  totals per backend and the latest problems.
- `--notify-command CMD` runs CMD after a run with a new signature or a missing suite summary,
  with `SEMANTIC_FUZZ_REPORT`, `SEMANTIC_FUZZ_NEW` and related variables set; outcomes go to
  `notify.log`.

**Known findings.** The driver lists the upstream findings recorded in `questions.md` whose
signatures are stable symptoms, each taken from a real occurrence. Their occurrences count and
are shown as known but never as new, so a fresh state reports only what `questions.md` does not
record; the same panic at another call site is new.
- Sonatina's demanded-bits overflow (`Integer overflow when casting to usize`) on O0, on O2 and
  in the Yul runs' O0 code images.
- Its O2 signextend-folding overflow (`arithmetic operation overflow`).
- solc's `StackTooDeepError` on Yul.
- The checked frontend's `SC0401` and `SC0406` rejection of a base method reached through two
  superclass bounds, on each backend.
- The fixtures' O2 crash.
- Hull's memory-range failure on a fixture source mutant's store at `2^256 - 1` that solc's Yul
  removes.

A mismatch's signature is its reduced program, so a recorded semantic defect is listed as a class
instead. A class names its backend, profile and stage, which paths disagree with which and their
shapes, and a structural property that the recorded reductions share: of the final plan for a
suite profile, of the paths' recorded observations for the fixtures. A finding counts under a
class by its own observations, a duplicate's included.
- Sonatina O0's class on `runtime-memory-values`: the EVM path returns another Word than original
  Core and Hull, which agree, and the final plan has a single loop that observes a bytes value or
  slice and later slices or writes one.
- The fixtures' `offset-by-first-allocations`: a source mutant whose paths differ only in
  returned words, exactly where their first allocations differ (Hull and solc at `0x80`, Sonatina
  O2 at `0x140`, O0 at `0x200`). Each differing word is one multiple `k` of the path's first
  allocation, `0 < |k| ≤ 4`, plus one constant on every path.
- At `e2eef194` neither the first class nor the fixtures' O2 crash occurs any more; both stay
  registered.
- Every other mismatch keeps its program signature and is new, including the same pattern on O2
  or Yul, and a source mutant whose words depend on the first allocations otherwise, such as a
  read of the pointer's slot one byte early.

**Exit statuses and limits.** The driver exits with status 2 when the tools are not ready or
another driver holds the state, 3 on an epoch change, 4 when the state reaches
`--max-state-bytes` (50 GiB by default) and 5 after three consecutive runs without a suite
summary.
- Signatures are conservative for mismatches: unrelated miscompilations share coarse
  fingerprints, so outside the recorded classes only the same reduced program counts as the same
  finding.
- A crash whose replay does not panic again records `not reproduced` as its call site.
- A signature need not survive an epoch change: when a comparison gains observations, as the
  stateful profiles did with
  [whole committed storage](SEMANTIC_DIFFERENTIAL.md#compare-whole-committed-storage), its
  mismatch fingerprints change and the same difference gets a new signature.

**Fixtures.** `--backend fixtures` is an opt-in run kind, alone or beside the suite backends. It
adds one run per iteration of the pinned
[fixtures](SEMANTIC_DIFFERENTIAL.md#compare-the-pinned-end-to-end-fixtures-across-paths) across
paths in mutation mode. That harness compares compiled paths with each other and with upstream's
recorded expectations, never with original Core.
- Iteration `i` runs `--fixture-count` fixtures (default 8) with root seed `base + i`. Each cycle
  of 23 iterations runs every fixture of the shard's pool once, in slices of a permutation seeded
  by the base seed and the cycle.
- Each fixture keeps at most `--fixture-mutants` mutants (default 32), a seeded sample of its four
  per step, and gets `--fixture-seconds` of wall time (default 300). The run gets
  `--fixture-run-seconds` (default 1,800), and `--fixture-jobs` fixtures (default 2) run at a time.
- Then each fixture runs at most `--fixture-sequences` sequence mutants (default 8; 0 runs none),
  each carrying one change forward through every later step, and at most `--fixture-sources`
  source mutants (default 2; 0 runs none), each changing one literal, operator, condition or
  inline Yul site.
- An entry past a budget has the status `budget`, and a fixture not started in time is
  unexecuted. Neither is a finding; the ledger counts both.
- Findings register with the backend `fixtures`: a compiler crash or path failure by its symptom,
  a path mismatch or unmet expectation by its fixture and reduced input, a sequence finding by its
  fixture, operator and reduced sequence, a source mutant's `compile-mismatch` by its stage, paths
  and symptom, and its step finding by its fixture, edit and reduced steps. A step finding in the
  first-allocation class registers under the class. The first examples keep the fixture's result
  record and the command that replays that fixture alone.
- The Sonatina O2 crash on `ignored-builtin-effects`, Hull's memory-range failure on a source
  mutant's store at `2^256 - 1` that solc's Yul removes, and the first-allocation class are listed
  as known. The O2 crash no longer occurs at `e2eef194`.
- Readiness also runs `semantic-fixtures.py --check`, and the epoch adds the digest of what it
  reports: the scripts, the compilers, the directive tools, the declaration and site extractors,
  the Lean runner, solc, Anvil, cast and the parity manifests. A state without fixtures keeps its
  epoch.
- Exports are cached in `.upstream/semantic-fixtures` and locked per fixture. `--cast` selects
  cast, and `--bin-dir` also selects the Lean runner.

**Remote hosts.** Use a Linux host with persistent disk, prepare the tools there once with
`--prepare --allow-network`, and run the driver under a service manager or `tmux`. Local
validation so far ran on macOS, so start with a short run on the host to check its toolchain.

## Workflow behavior

- Automatic triggers are disabled for now, because hosted runs take too long: pull requests,
  pushes to `main` and the daily schedule start no run.
- Manual dispatch runs the full Lean build and tests, the kernel policy, the Python policy tests,
  all fixed corpora, the controlled finding check and new seeds. It accepts an optional unsigned
  64-bit root seed; otherwise random runs use the GitHub run number.
- Restoring the `pull_request`, `push` and `schedule` triggers brings back the fixed gate for pull
  requests and `main` pushes and the daily seed exploration at 18:23 UTC, where a replaced
  pull-request run cancels its predecessor.
- Every action is pinned to a commit, and jobs have read-only repository permissions.
- The proof job removes the unused Android and .NET SDKs, only on its disposable GitHub-hosted
  runner, to make room for the complete proof build. The differential job prepares its tools
  separately, and neither job uses a pre-existing chain.
- Reports, cases and finding archives are uploaded even after failure and expire after fourteen
  days. Promote confirmed minimized regressions to tracked tests before they expire.
- Keep unresolved upstream questions in the local, ignored `questions.md`. Do not upload or
  commit that file.
- Hosted execution begins when the workflow is pushed to GitHub. Local validation of its commands
  and workflow syntax does not establish that a hosted run has completed.
