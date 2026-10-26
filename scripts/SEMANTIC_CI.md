# Running the semantic test suite

The [workflow](../.github/workflows/semantic.yml) runs the existing differential
campaigns. It does not replace their Core reference, runtime adapters, reduction
or replay rules. The [implementation roadmap](../docs/design/next-implementation-roadmap.md)
records the scope and subsequent priorities.

## Tools

Install Python 3.11 or newer, Git, Rust 1.97.0 through rustup, the toolchain in
`lean-toolchain` through elan, and Anvil 1.5.1. The EVM hardfork is Osaka. The
bootstrap verifies these versions and never installs system tools itself.
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
offline and the fourteen native Lean tools in one Lake invocation. Existing
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

Use `--backend sonatina-o2` with either suite command to compare the same cases
after O2 compilation. O0 remains the default. The CI matrix runs each backend
in a separate job with separate reports and artifacts; failure in one does not
cancel the other. Random generation uses the same recorded seeds independently
of backend selection, so optimization does not change the generated inputs.

`--backend yul` selects the fourteen pure profiles by default (595 fixed cases).
Explicitly selecting a stateful profile fails before execution. Each random
Yul run with `--cases 16` requests 224 cases. The shared preparation command
builds Rust and Lean tools; solc is supplied and checked separately.

| Backend | Fixed cases/scenarios | EVM execution | Imported Hull code images |
| --- | ---: | --- | --- |
| `sonatina-o0` | 690 | Sonatina O0 | Sonatina O0 |
| `sonatina-o2` | 690 | Sonatina O2 | Sonatina O2 |
| `yul` | 595, pure only | Optimized solc Yul, Osaka | Sonatina O0 |

All rows use the original generated Core as the primary reference. Yul's
linked layout is not supplied to the Hull importer. Its pure result can still
be compared with both other paths; code-dependent and stateful Yul observations
remain unsupported. Reports record this distinction in `pathBackends`.

The default selection is all twenty-one profiles: fourteen pure profiles,
storage, storage rollback, parent/child calls, keyed storage, dynamic arrays,
event logs and call value. Fixed mode runs all 690 manifest cases or scenarios. It rejects `--cases` and `--nodes` overrides rather
than silently truncating required coverage. Repeat `--profile NAME` to select a
smaller suite.

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
do not describe that as exact replay of the earlier environment.

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

## Workflow behavior

Pull requests and pushes to `main` run the full Lean build/tests, kernel policy,
Python policy tests, all fixed corpora and the controlled finding check. The
daily run at 18:23 UTC also explores new seeds. Manual dispatch accepts an
optional unsigned 64-bit root seed; otherwise random runs use the recorded
GitHub run number. Every action is pinned to a commit, and jobs have read-only
repository permissions. Replaced pull-request runs cancel their predecessors.

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
