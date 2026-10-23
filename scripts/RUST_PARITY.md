# Rust runtime compatibility checks

The reference checkout is `.upstream/solcore-rs-20261023` at
`2a745e12974c373c3799fec81b48a53c7dce2ab4`. All manifests pin both the revision
and each fixture's source hash. The tools reject a different revision or an
unexpected tracked edit to that checkout. They do not modify the sibling Rust
repository.

## Build the import tools

The checked Hull exporter must already be built with
`python3 scripts/export-rust-hull.py --build`. Build the additional tools with:

```sh
python3 scripts/export-rust-code-image.py --build
python3 scripts/export-rust-directives.py --build
python3 scripts/build-rust-directive-resolver.py
```

These commands build small packages against the pinned upstream dependencies.
They use Cargo offline and share `.upstream/rust-parity-target`. The original
compiler checking pipeline remains enabled. The code-image tool compiles actual
Sonatina O0 bytes and linker extents; it never executes EVM instructions.

## Execute the inventories

```sh
python3 scripts/rust-contract-parity.py --reuse-exports --output .upstream/contracts.json
python3 scripts/rust-scenario-parity.py --reuse-exports --output .upstream/scenarios.json
python3 scripts/rust-method-parity.py --reuse-exports --output .upstream/methods.json
```

- The first gate has 172 calls from 22 fixtures. Each starts with fresh storage
  and does not execute a constructor.
- The raw scenario gate covers 72 fixtures, with 72 constructors and 626 ordered
  transactions. Successful calls retain state; reverts discard changes.
- The method gate covers the remaining 96 fixtures, with 96 constructors and
  618 directives. Ordinary directives discard state changes, matching upstream
  `eth_call`; `send` directives retain state and require success. Constructor
  and send callers match the standard Anvil account. Ordinary calls use zero
  because the upstream JSON-RPC request omits `from`.

The Rust parser and `test-directives` crate supply exact raw expectations and
method ABI encoding. The driver supplies each method's ABI; `cast sig` computes
its selector. Lean imports the checked typed Hull, checks the generated Core,
and executes it. No source evaluator or EVM executes these checks.

Use `--fixture 'pattern'` to select fixtures. The two deployment gates accept
`--call-prefix N` to execute an ordered prefix while preserving earlier state.
`--report-only` collects failures and returns zero for inventory work; it does
not change the report's `passed` field. A rejected import, resource limit or
unexecuted call never counts as a matching expectation.

Reports record constructor and call results separately. Returned and reverted
payloads must match exactly unless the upstream directive explicitly permits
any payload. Code bytes returned by constructors must match the selected linked
runtime image. Available gas is supplied only by explicit manifest entries and
is not an EVM gas meter. Two fixtures use explicit Core-step limits: `basic`
uses 15,000,000 after its constructor measured 11,032,131 transitions, and
`deposit` uses 25,000,000 after 16,525,108 transitions. Other fixtures retain
the 10,000,000-step default. Missing account behavior remains an explicit failure.

## Execute the Rust EVM reference

```sh
python3 scripts/rust-evm-reference.py --build --build-only
python3 scripts/rust-evm-reference.py --output .upstream/evm-reference.json
```

This separate gate runs the unchanged upstream E2E test harness on local Anvil.
It builds only the Sonatina and Yul E2E binaries in
`.upstream/evm-reference-target`, with the upstream `e2e` profile, locked offline
dependencies and Cargo incremental compilation disabled. Existing import-tool
binaries and receipts remain separate. Anvil, cast and solc must be installed,
and the execution environment must permit localhost connections.

Every selected fixture runs with `E2E=1 E2E_REQUIRED=1` and the Osaka hardfork.
The pipeline-only flag is removed. Sonatina executes both O0 and O2; the Yul
backend executes solc output built with `--strict-assembly --optimize`. The
upstream harness supplies constructor inputs, calls and expectations. Missing
tools, ignored tests and an empty test selection cannot count as execution.
Use `--backend sonatina` or `--backend yul`, and `--fixture 'pattern'`, to narrow
the run. `--report-only` retains failures in the report while returning zero.

Reports retain every test's output and exit code, its failure stage, source and
binary hashes, required environment flags and tool versions. This verifies the
Rust reference separately from the Core gates. The two paths compare against
the same upstream directives; the report does not claim a direct trace-by-trace
comparison or semantic equivalence beyond those tests.

After a completed build, `evm-reference-target/e2e` is disposable compilation
output. Keep `evm-reference-target/bin` and `build.json` to rerun the checks
without rebuilding. Temporary Yul and process logs are owned and removed by
the upstream harness.

The 2026-10-24 reference run passed all 168 Sonatina fixtures at O0 and O2 and
all 168 Yul fixtures, without failures or skips. It used Rust 1.97.0,
Anvil/cast 1.5.1-stable, solc 0.8.35 and Osaka. The full local report is
`.upstream/evm-reference-final-168.json`; its recorded runner source is retained
as `.upstream/evm-reference-runner-used.py`. The current runner additionally
recognizes Yul-specific skip messages; this was tested after the recorded run.
See Q008 and Q010 for three fixtures accepted by these test entry points and
rejected by the checked public compiler used for Core imports.

## Check the harness itself

```sh
python3 scripts/test-rust-contract-parity.py
python3 scripts/test-rust-scenario-parity.py
python3 scripts/test-rust-method-parity.py
python3 scripts/test-rust-evm-reference.py
```

Export caches include source, binary, dependency-lock and output hashes. A stale
receipt causes rejection or a fresh export. Temporary JSON inputs and compiler
outputs are removed after use. Keep exporter binaries and receipts for reuse;
completed Cargo incremental directories and superseded reports can be removed.
Current gaps and policy decisions are recorded in [questions.md](../questions.md).
