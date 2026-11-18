# Rust runtime compatibility checks

These gates run the pinned Rust compiler's own end-to-end fixtures: on Lean Core through the
checked Hull import, and separately on the EVM through upstream's harness. The reference checkout
is `.upstream/solcore-rs-20261116` at `d1b5ac28c0a5821c1a56758f182e27bc5e7c4f09`. Every manifest
pins both the revision and each fixture's source hash. The tools reject a different revision or an
unexpected tracked edit to that checkout, and they never modify the sibling Rust repository.

Run records up to 2026-11-17 are in git history at `049f8ce1f`.

## Build the import tools

The checked Hull exporter must already be built with `python3 scripts/export-rust-hull.py
--build`. Build the other tools with:

```sh
python3 scripts/export-rust-code-image.py --build
python3 scripts/export-rust-directives.py --build
python3 scripts/build-rust-directive-resolver.py
python3 scripts/export-rust-declarations.py --build
python3 scripts/export-rust-sites.py --build
```

- These commands build small packages against the pinned upstream dependencies, with Cargo
  offline, sharing `.upstream/rust-parity-target`.
- `prepare-semantic-tools.py --prepare` also builds the directive extractor and resolver and the
  declaration and site extractors offline, and its receipt covers all four
  ([suite preparation](SEMANTIC_CI.md#tools)).
- The original compiler checking pipeline stays enabled.
- The code-image tool compiles actual Sonatina bytes and linker extents; it never executes EVM
  instructions. The default optimization is O0, and `--optimization O2` selects the real O2
  pipeline. Both levels use the same pinned backend and pass the same strict image checks.

## Execute the inventories on Core

```sh
python3 scripts/rust-contract-parity.py --reuse-exports --output .upstream/contracts.json
python3 scripts/rust-scenario-parity.py --reuse-exports --output .upstream/scenarios.json
python3 scripts/rust-method-parity.py --reuse-exports --output .upstream/methods.json
```

- **Contract gate:** 172 calls from 22 fixtures. Each call starts with fresh storage and runs no
  constructor.
- **Raw scenario gate:** 77 fixtures, with 77 constructors and 697 ordered transactions.
  Successful calls keep their state; reverts discard their changes.
- **Method gate:** the remaining 107 fixtures, with 107 constructors and 828 directives. Ordinary
  directives discard their state changes, matching upstream's `eth_call`; `send` directives keep
  them and must succeed. Constructor and send callers are the standard Anvil account. Ordinary
  calls use zero, because the upstream JSON-RPC request omits `from`.

How the gates work:
- The Rust parser and the `test-directives` crate supply the exact raw expectations and the method
  ABI encoding. The driver supplies each method's ABI, and `cast sig` computes its selector.
- Lean imports the checked typed Hull, checks the generated Core and executes it. No source
  evaluator or EVM executes these checks.
- `--fixture 'pattern'` selects fixtures. The two deployment gates accept `--call-prefix N` to run
  an ordered prefix while keeping earlier state. `--report-only` collects failures and returns
  zero for inventory work; it does not change the report's `passed` field.
- A rejected import, a resource limit or an unexecuted call never counts as a matching
  expectation.
- Reports record constructor and call results separately. Returned and reverted payloads must
  match exactly unless the upstream directive explicitly permits any payload. Code bytes returned
  by a constructor must match the selected linked runtime image.
- Available gas comes only from explicit manifest entries; it is not an EVM gas meter.
- Missing account behavior remains an explicit failure.

Core-step limits default to 10,000,000. Three fixtures set their own, each above its constructor's
measured need:

| Fixture | Limit | Constructor needed |
| --- | ---: | --- |
| `basic` | 15,000,000 | 11,032,131 transitions |
| `deposit` | 25,000,000 | 16,525,108 transitions |
| `closure-parameters` | 15,000,000 | between 10,000,000 and 10,500,000 at `e2eef194`, which added 13 of its 49 calls |

## Execute the Rust EVM reference

```sh
python3 scripts/rust-evm-reference.py --build --build-only
python3 scripts/rust-evm-reference.py --output .upstream/evm-reference.json
```

This separate gate runs the unchanged upstream E2E test harness on a local Anvil.
- It builds only the Sonatina and Yul E2E binaries, in `.upstream/evm-reference-target`, with the
  upstream `e2e` profile, locked offline dependencies and Cargo incremental compilation disabled.
  The import tools' binaries and receipts stay separate.
- Anvil, cast and solc must be installed, and the environment must permit localhost connections.
- Every selected fixture runs with `E2E=1 E2E_REQUIRED=1` and the Osaka hardfork, without the
  pipeline-only flag. Sonatina executes both O0 and O2; the Yul backend executes solc output built
  with `--strict-assembly --optimize`. The upstream harness supplies constructor inputs, calls and
  expectations.
- Missing tools, ignored tests and an empty test selection cannot count as execution.
- `--backend sonatina` or `--backend yul` and `--fixture 'pattern'` narrow the run.
  `--report-only` keeps failures in the report while returning zero.
- Reports keep every test's output and exit code, its failure stage, source and binary hashes,
  required environment flags and tool versions.
- This verifies the Rust reference separately from the Core gates. Both compare against the same
  upstream directives; the report claims no direct trace-by-trace comparison and no semantic
  equivalence beyond those tests.
- After a completed build, `evm-reference-target/e2e` is disposable. Keep
  `evm-reference-target/bin` and `build.json` to rerun without rebuilding. The upstream harness
  owns and removes its temporary Yul and process logs.
- The runner recognizes Yul-specific skip messages.
- Q008 and Q010 recorded three fixtures that these test entry points accepted and the checked
  public compiler used for Core imports rejected. Both are resolved at `e2eef194`.

## Compare the fixtures across compiled paths

[semantic-fixtures.py](semantic-fixtures.py) starts from the checked driver's output instead:
each fixture's checked Hull, its Sonatina O0 and O2 code images and its Yul. It compares the
recorded steps and seeded mutants across those four paths
([pinned fixtures](SEMANTIC_DIFFERENTIAL.md#compare-the-pinned-end-to-end-fixtures-across-paths)).
- On that route the code-image tool crashed at O2 on `ignored-builtin-effects` at `2a745e12`,
  which the in-memory upstream harness passed; the crash is a recorded finding.
- Since `e2eef194`, whose Sonatina carries upstream's fix of that fixture, every pinned fixture
  compiles on every path.
- The fuzz driver can run this comparison as an opt-in run kind
  ([continuous fuzzing](SEMANTIC_CI.md#continuous-fuzzing)).

## Check the harness itself

```sh
python3 scripts/test-rust-contract-parity.py
python3 scripts/test-rust-scenario-parity.py
python3 scripts/test-rust-method-parity.py
python3 scripts/test-rust-evm-reference.py
```

- Export caches include source, binary, dependency-lock and output hashes. A stale receipt causes
  a rejection or a fresh export.
- Temporary JSON inputs and compiler outputs are removed after use. Keep the exporter binaries and
  receipts for reuse; completed Cargo incremental directories and superseded reports can be
  removed.
- Current gaps and policy decisions are recorded in [questions.md](../questions.md).

## Account and recursive-layout gates

The Core runtime lowers all 81 wrappers in the pinned `std/opcodes.sol`.
- `Contract.Context.ambient` supplies transaction and block observations, and `Context.world`
  account storage, nonce and code. A complete world makes omitted accounts empty; an incomplete
  world diagnoses unknown accounts.
- Executable byte images must have corresponding checked Hull frames in the catalogue. Arbitrary
  bytecode and unsupported precompiles produce explicit failures. Gas is not metered.
- Q009 to Q012 in `questions.md` specify these boundaries.

The aggregate Lean test executable covers ambient reads, account inspection,
CALL/CALLCODE/DELEGATECALL/STATICCALL, CREATE/CREATE2, delayed SELFDESTRUCT, transaction rollback,
world persistence and repeated fuel resumption. Large image comparisons keep exact byte equality,
including sparse mappings and first-duplicate semantics. The largest deployed image is tested
within the existing fuel budget, and aligned snapshots traverse the source mapping once.

For focused public API tests:

```sh
lake env lean --run Tests/RustHullWorldRun.lean
lake env lean --run Tests/RustHullCreationAccountsRun.lean
python3 scripts/evm-account-reference.py --help
python3 scripts/test-rust-recursive-layouts.py --evm-reference
python3 scripts/test-rust-opcode-wrappers.py
```

- **Opcode wrapper gate:** exports fresh checked Hull from a source fixture that calls all 20 added
  standard-library wrappers. It checks that the calls and standard assembly bodies survive export,
  then actual Core results and state changes, missing ambient inputs and static restrictions. It
  reuses the pinned exporter and removes its temporary files.
- **Account reference gate:** uses actual solc and Anvil execution on Osaka. Its 67 observations
  and 11 address vectors are checked in under `Tests/Fixtures/EvmAccounts/`, and the Lean tests use
  the same exact target and init images and expected account behavior.
- **Recursive-layout gate:** since solcore-rs #130 the checked compiler refuses, with `SC0420` and
  before backend emission, every concrete recursive layout that would need boxing. The gate checks
  that refusal: the checked export refuses the dynamic constructor/relay/match fixture, the two
  cases that once failed in both upstream backends and the two upstream layouts that `2a745e12`
  still exported as finite. With `--evm-reference`, Sonatina and Yul emission refuse the three
  local fixtures too. `Tests.RustHullRecursiveCorrespondence` still covers Lean's recursive Hull
  representation.

`AccountState.definitions` checks successful contract compilation, explicit code catalogues
included. Public initialization typing covers the actual world and ambient literals. Run and
resume safety excludes Core machine faults while allowing revert, language failure, export limits
and exhausted fuel. These safety results do not establish Rust source-to-Hull preservation,
Hull/EVM semantic equivalence or consensus gas accounting.
