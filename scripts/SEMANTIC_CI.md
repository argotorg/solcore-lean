# Running the semantic test suite

The [workflow](../.github/workflows/semantic.yml) runs the existing differential
campaigns. It does not replace their Core reference, runtime adapters, reduction
or replay rules. The [implementation roadmap](../docs/design/next-implementation-roadmap.md)
records the scope and subsequent priorities.

## Tools

Install Python 3.11 or newer, Git, Rust 1.97.0 through rustup, the toolchain in
`lean-toolchain` through elan, and Anvil 1.5.1. The EVM hardfork is Osaka. The
bootstrap verifies these versions and never installs system tools itself.
The stateful comparisons enumerate EVM storage from Anvil's prestate diffs;
after changing Anvil, run `python3 scripts/check-evm-storage-diff.py`, which
checks on probe contracts that those diffs report every changed slot.
For Yul comparisons also install solc `0.8.35+commit.47b9dedd`; use `--solc`
to choose its path. The Yul exporter checks its full version and binary hash.
The CI Yul job downloads the Linux amd64 release from the
[official binary inventory](https://binaries.soliditylang.org/linux-amd64/list.json)
and verifies the pinned SHA256 before making it executable.

```sh
python3 scripts/prepare-semantic-tools.py --plan
python3 scripts/prepare-semantic-tools.py --prepare --allow-network
python3 scripts/prepare-semantic-tools.py --verify
```

Preparation fetches the exact pinned Rust revision into a new directory, checks
its tracked files, and fetches locked dependencies. It builds the two exporters
offline and the twenty-nine native Lean tools in one Lake invocation. Existing
checkouts with another revision or unrelated edits are rejected. Network
access requires `--prepare --allow-network`; omit `--allow-network` to prepare
using existing dependency downloads. Verification is read-only and offline.

The readiness receipt hashes tool executables, native sources, exporter sources,
dependency locks and build receipts. Changed inputs or binaries require fresh
preparation. It does not accept a cache merely because its directory exists.
The CI cache contains dependency downloads, not executable proof artifacts or
saved expected results. Cargo incremental compilation and debug information are
disabled in CI to limit disk use.

## Fixed and random suites

```sh
python3 scripts/semantic-suite.py --mode fixed \
  --seconds 7200 --profile-seconds 900 --output .upstream/semantic-fixed
python3 scripts/semantic-suite.py --mode random --seed 20261026 \
  --cases 16 --attempts 2048 --seconds 3600 --profile-seconds 600 \
  --output .upstream/semantic-random
```

Random mode also accepts `--nodes-scale S`, from 1 to 4, which multiplies each
profile's default node budget, capped at 512; an explicit `--nodes` wins.

Random campaigns of the sixteen G0-based pure profiles generate with [G0
revision four](SEMANTIC_DIFFERENTIAL.md#g0-generator-revisions)
(`core-g0-v4/lcg64-v1`): revision two under a per-case swarm mask, restricted
to the features the profile's emitter renders. The random steps of every
stateful profile generate with revision three (`core-g0-v3/lcg64-v1`), the same
mask without that restriction; the stateful tools refuse revision four. In the
eleven runtime-input profiles whose functions can be identities, random
campaigns also apply the acceptance filter `exclude-boundary-identity-v1`, which
excludes a function that returns every boundary input unchanged
([boundary identities](SEMANTIC_DIFFERENTIAL.md#boundary-identities)). Random
runtime-input cases run each function at its boundary inputs and then at four
seed-derived inputs, and random stateful scenarios have eight transactions.
Fixed corpora and saved cases keep the revision, inputs and sequence they
record. Each profile row of the report lists `generatorVersions`,
`inputSelections`, `acceptances` and `transactions` under `campaign.generation`; the suite
does not select other values. `--cases` counts a function's inputs separately,
so a random run of a runtime-input profile covers a function per eight to
twelve cases, and its last function may lose inputs. `--functions N` instead
gives every random runtime-input pure profile N whole functions with all of
their inputs, while `closed-g0` and the stateful profiles keep `--cases`; the
report records N in `functions`. A campaign returns at most 1,024 cases, so N
is at most 85 while a twelve-input profile is selected. Without `--attempts`,
`--functions N` also gives each of those profiles at least 16 attempts per
function, up to 10,000. One generation response is limited to 2 MiB, so a
larger request is generated in several requests of whole functions that
continue the same seed sequence and merge to the same cases; only a function
whose cases alone exceed 2 MiB stops at generation as an inconclusive
`output-limit` ([whole functions](SEMANTIC_DIFFERENTIAL.md#seeded-runtime-inputs)).

Use `--backend sonatina-o2` with either suite command to compare the same cases
after O2 compilation. O0 remains the default. The CI matrix runs each backend
in a separate job with separate reports and artifacts; failure in one does not
cancel the other. Random generation uses the same recorded seeds independently
of backend selection, so optimization does not change the generated inputs.

`--backend yul` selects the twenty pure profiles by default (1,018 fixed
cases). The eighteen storage-family profiles also run on Yul when `--profile`
selects them, with 227 fixed scenarios
([storage-family contracts on Yul](SEMANTIC_DIFFERENTIAL.md#compare-storage-family-contracts-on-yul));
selecting either call profile fails before execution. Each random Yul run of
the default selection with `--cases 16` requests 320 cases. The shared
preparation command builds Rust and Lean tools; solc is supplied and checked
separately.

| Backend | Fixed cases/scenarios | EVM execution | Imported Hull code images |
| --- | ---: | --- | --- |
| `sonatina-o0` | 1,273 | Sonatina O0 | Sonatina O0 |
| `sonatina-o2` | 1,273 | Sonatina O2 | Sonatina O2 |
| `yul` | 1,018 pure; 227 storage-family when selected | Optimized solc Yul, Osaka | Sonatina O0 |

All rows use the original generated Core as the primary reference. Yul's
linked layout is not supplied to the Hull importer. Its pure and
storage-family results can still be compared with both other paths, because
those observations do not depend on code layout; code-dependent observations
and the two call profiles remain unsupported on Yul. Reports record this
distinction in `pathBackends`.

The default selection is all forty profiles: twenty pure profiles, storage,
storage rollback, parent/child calls, keyed storage, dynamic arrays, event
logs, call value, bounded bytes, forwarded value, Keccak-addressed mappings, a
sender-keyed ledger, 256-byte `bytes` payloads, nested `uint256[][]` inputs,
malformed calldata for the dynamic-array, nested-array and 256-byte `bytes`
contracts, a contract with several external methods, a bounded loop over
declared slots, a bounded loop over Keccak-addressed mapping entries that logs
each iteration, and a method that returns a static tuple of two to four Words.
Fixed mode runs all 1,273 manifest cases or scenarios. It rejects `--cases`,
`--functions` and `--nodes` overrides rather than silently truncating required
coverage. Repeat `--profile NAME` to select a smaller suite.

Random mode derives each profile's starting seed from the root seed, profile,
shard index/count and the recorded derivation version. `--shard-index` and
`--shard-count` define reproducible independent search starting points; they do
not claim mathematically disjoint generated programs. Every shard runs every
selected profile. Generation attempts and exclusions remain in the report.
The suite does not retry rejected source as if it had never been generated.

Profiles run sequentially. The suite bounds total and per-profile time and
disk use, subprocess output, generation, case execution and reduction. Defaults
allow 1 GiB for the entire suite and 256 MiB for one profile. Limits bound suite
outputs, not the separately prepared toolchains and build caches. SIGTERM and
keyboard interruption stop owned processes, including compiler and Anvil
children in separate process groups, and record unfinished work.

Only complete actual agreement and required coverage produce exit status zero.
Findings, missing results, generation exhaustion and resource exhaustion return
nonzero. A mismatch found before a later interruption stays a finding. Reports
include per-profile elapsed time, accepted/excluded/executed/matched counts and
measured case throughput; these are not runtime opcode coverage measurements.

## Findings and replay

Successful campaigns keep cases and compact reports, removing disposable
exports. Findings retain full original and reduced archives and their failure
fingerprints. Use the corresponding pure, storage or call adapter to replay
the archive. Exact replay requires the recorded tools and pinned library
identities. With changed tools, start a new comparison from the saved case;
do not describe that as exact replay of the earlier environment. A pure
campaign compiles each distinct source once per backend and shares it among
cases whose source files, backend, library, exporters and compiler builds match
by digest; every archive still holds its own copies of the outputs and records
the shared compilation in `report.compilation`, and exact replay compiles
again.

The CI finding check uses a reducible fixed addition case:

```sh
python3 scripts/check-semantic-findings.py \
  --case .upstream/semantic-fixed/00-closed-g0/cases/0006.json \
  --output .upstream/semantic-findings
```

This check introduces a synthetic difference only in a separate analysis after
real agreement. It requires an accepted reduction, exact replay of the reduced
actual archive, reproduction of the synthetic fingerprint, and an actual
fuel-one run classified as inconclusive. The original runtime observations
remain untouched. A compiler or runtime failure during this check fails it.
The check also accepts `--backend sonatina-o2`; reduced cases and exact replay
retain that selection, including its mismatch fingerprint.
Use `--backend yul [--solc PATH]` for the same check with actual Yul compilation.
Yul archives also retain the checked Yul, exact solc request/response, both
bytecodes and matching Hull/source/tool receipts. Replay verifies these files
locally, so a moved archive does not depend on its original source directory.

## Continuous fuzzing

`scripts/semantic-fuzz.py` runs the random suite repeatedly on one machine and
keeps a registry of what it finds. Prepare the tools first, then start it:

```sh
python3 scripts/semantic-fuzz.py run --state .upstream/semantic-fuzz \
  --base-seed 20261101 --shard-index 0 --shard-count 1
python3 scripts/semantic-fuzz.py report --state .upstream/semantic-fuzz
python3 scripts/semantic-fuzz.py label --state .upstream/semantic-fuzz SIGNATURE 'triage note'
```

Iteration `i` runs the suite in random mode once per backend, with root seed
`base + i`, so the backends compare the same generated programs. All three
backends run by default. On Yul the driver runs the pure and the eighteen
storage-family profiles, whether profiles are configured or not, and never the
two call profiles. It selects the storage family explicitly, since the suite's
own Yul default is the pure profiles. With the default sixteen cases, this adds
288 eight-transaction scenarios to each Yul iteration, about 3,000 seconds at
the default node budgets and 3,100 at doubled ones. No storage-family profile
took more than 222 seconds of its 900. Machines that share
a base seed use their own `--shard-index` of a common `--shard-count`. The
first `run` fixes the configuration in `config.json`: backends, profiles,
cases (default 16), whole functions (`--functions`, unset by default),
attempts (2,048), node-budget scales, time and disk limits and tool paths. `--size-cycle 1,2` (the default) gives iteration `i` the scale
at position `i` modulo the cycle, so every other iteration doubles each
profile's default node budget, capped at 512, and generates larger programs.
Later runs resume after the last recorded run and refuse different options;
use a new state directory for another configuration. `--iterations N` stops
after N iterations, a `STOP` file in the state directory stops before the next
run, and SIGTERM or SIGINT stops the running suite, which records its
unfinished work. An interrupted run moves to `interrupted/` and reruns from its
seed on the next start; its partial findings are not counted.

`--jobs N` runs N suites at once, each on its own iteration and backend. Seeds
still follow the iteration, so results do not depend on N. Runs finish out of
order: the ledger records them as they complete, and a resumed driver fills
gaps before starting new iterations. Each suite runs one compiler, one Anvil
and the Lean tools at a time. Choose N by the host's cores and memory; an
overloaded host turns case timeouts into inconclusive results.

Before every run the driver verifies the prepared tools offline. The digests
of the readiness receipt and of the harness scripts form an epoch. When the
tools or scripts change, the driver stops until it is restarted with
`--accept-new-epoch`, and the ledger records each run's epoch.

Every run appends a line to `ledger.jsonl` with its seeds, statuses, counts,
finding occurrences and problems. Each occurrence is counted in
`registry.json` under a signature made of the backend, category and stage
plus one of:

- for compiler crashes, rejections and other tool failures, the first panic
  location and message, or the first error line, without paths, thread
  identifiers or numbers. For a panic the driver also replays the failing Rust
  stage from a scratch copy of the archive with `RUST_BACKTRACE=1` and adds the
  first two frames outside the panic machinery and the panicking library, so
  panics raised at one library location by different compiler code count
  separately. The replay never revisits the run's classification;
  `--no-crash-replay` turns it off;
- for semantic mismatches, the profile, the rest of the mismatch fingerprint
  and the reduced program's digest.

The first `--examples` occurrences of a signature (default three) keep their
complete archives under `findings/SIGNATURE/` with an `occurrence.json`. Later
occurrences are counted with their seeds, from which random cases replay with
the tools and scripts of the run's epoch; the ledger also records each
profile's generator versions, input selections and transaction count, and for
pure profiles the distinct sources, compilations and reused compilations.
Runs that pass are deleted. Other runs keep their suite summary and the
summaries and logs of the profiles that did not pass. A profile that did not
pass without a finding, or was left unexecuted, is listed as a problem.

`label` records a triage note for a signature in `labels.json`. A labelled
signature is shown as known; it stays counted and listed, and its new
occurrences still enter the ledger. `report.md` and `report.json` list the
signatures (untriaged first, new ones marked), the run totals per backend and
the latest problems. `--notify-command CMD` runs CMD after a run with a new
signature or a missing suite summary, with `SEMANTIC_FUZZ_REPORT`,
`SEMANTIC_FUZZ_NEW` and related variables set; outcomes go to `notify.log`.

The driver exits with status 2 when the tools are not ready or another driver
holds the state, 3 on an epoch change, 4 when the state reaches
`--max-state-bytes` (50 GiB by default) and 5 after three consecutive runs
without a suite summary. Signatures are conservative for mismatches: unrelated
miscompilations share coarse fingerprints, so only the same reduced program
counts as the same finding. A crash whose replay does not panic again records
`not reproduced` as its call site. A signature need not survive an epoch
change: when a comparison gains observations, as the stateful profiles did with
[whole committed storage](SEMANTIC_DIFFERENTIAL.md#compare-whole-committed-storage),
its mismatch fingerprints change and the same difference gets a new signature.

On a remote machine, use a Linux host with persistent disk, prepare the tools
there once with `--prepare --allow-network`, and run the driver under a
service manager or `tmux`. Local validation so far ran on macOS, so start with
a short run on the host to check its toolchain.

## Workflow behavior

Automatic triggers are disabled for now because hosted runs take too long:
pull requests, pushes to `main` and the daily schedule start no run. Manual
dispatch runs the full Lean build/tests, kernel policy, Python policy tests, all
fixed corpora, the controlled finding check and new seeds. It accepts an
optional unsigned 64-bit root seed; otherwise random runs use the recorded
GitHub run number. Restoring the `pull_request`, `push` and `schedule` triggers
in the workflow brings back the fixed gate for pull requests and `main` pushes
and the daily seed exploration at 18:23 UTC, where a replaced pull-request run
cancels its predecessor. Every action is pinned to a commit, and jobs have
read-only repository permissions.

The proof job removes the unused Android and .NET SDKs only on its disposable
GitHub-hosted runner to make room for the complete proof build. The differential
job prepares its tools separately. Neither job uses a pre-existing chain.

Reports, cases and finding archives are uploaded even after failure and expire
after fourteen days. Promote confirmed minimized regressions to tracked tests
before artifact expiry. Keep unresolved upstream questions in the local,
ignored `questions.md`. Do not upload or commit that file.

Hosted execution begins when the workflow is pushed to GitHub. Local validation
of its commands and workflow syntax does not establish that a hosted run has
completed successfully.
