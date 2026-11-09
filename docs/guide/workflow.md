# Workflow

This page says how to build, test and check a change, and when to run what. README's
[Build and test](../../README.md#build-and-test) section has the three basic commands.

## Requirements

- Lean and Lake at the version in [`lean-toolchain`](../../lean-toolchain).
- Node.js, for the kernel check.
- Python 3.11 or later, for the scripts.
- For the differential tests only: the pinned Rust toolchain, solc and Anvil.
  `python3 scripts/prepare-semantic-tools.py --plan` prints the versions they need.

## While you work

- **Build what you touched.**
  - `lake build Solcore.Core.Safety` builds one module and what it imports.
  - `lake build Solcore.Core` builds an area through its umbrella.
  - `lake build` builds the whole library, every module under `Solcore/`.
- **Expect long rebuilds after changes low in the stack.**
  - A change to Syntax, Core or TypeSystem rebuilds nearly everything above it.
  - A full build takes about half an hour on a ten-core machine.
  - Batch such changes, and build the whole library at the end.
- **Run the tests.**
  - `lake test` builds and runs the test driver `solcore-tests` ([`Tests/Main.lean`](../../Tests/Main.lean)).
  - [Tests](tests.md) says how the tests are organized.
- **Executables.**
  - Each case tool and runner of the differential tests is a `lean_exe` in
    [`lakefile.lean`](../../lakefile.lean).
  - `lake build <name>` builds one of them.

## Before you commit

These are the checks of CI's `checks` job, in
[`.github/workflows/semantic.yml`](../../.github/workflows/semantic.yml):

```sh
node scripts/check-kernel.mjs
for test in scripts/test-semantic-*.py scripts/test-prepare-semantic-tools.py scripts/test-export-rust-*.py; do
  python3 "$test"
done
git diff --check
lake build
lake test
```

Keep each commit to one logical change with its verification. Do not mix an unrelated proof change
into a change to the differential harness.

## When you touch the differential tests

- **Prepare and verify the tools.**
  - `python3 scripts/prepare-semantic-tools.py --prepare` rebuilds stale tools from the pinned
    checkouts under `.upstream/`, which Git ignores.
  - It fetches only with `--allow-network`, which a fresh checkout needs once.
  - `--verify` is a read-only readiness check.
- **Validate the corpora you changed.**
  - `Tests/scripts/test-semantic-*-corpus.py` check fixed corpora with the native tools, without an
    EVM.
  - For example: `python3 Tests/scripts/test-semantic-corpus.py --manifest scripts/semantic-loop-corpus.json`.
- **Check the fixtures** with `python3 scripts/semantic-fixtures.py --check`.
- **Run the other harnesses.** Some `scripts/test-*.py` files are not in CI's list. They include the
  source-to-Rust harnesses (`test-source-*-rust.py`), which run Lean's source semantics against the
  Rust compiler.
- **Run suites.** `scripts/semantic-suite.py` runs the fixed and random suites. See
  [`scripts/SEMANTIC_CI.md`](../../scripts/SEMANTIC_CI.md) and
  [Differential testing](differential-testing.md).

## Refactoring without changing declarations

The tools in [`scripts/refactor/`](../../scripts/refactor/) check that a change moves declarations
and changes nothing else.

- **`snapshot.py take OUT.jsonl`** writes one record per constant of the built library:
  - its name and kind;
  - hashes of its type and, except for theorems, its value;
  - its flags: simp sets, instance priority, reducibility and others.

  The record notes the defining module, but `diff` ignores it. `take` refuses to run on a stale
  build.
- **`snapshot.py diff A.jsonl B.jsonl [--renames FILE]`** exits non-zero on any added, removed or
  changed declaration. Take a snapshot before the change, and require an empty diff after it.
- **`leanmerge.py`** merges and moves modules (`merge`, `move`), reports import structure
  (`graph`) and estimates name clashes (`clashes`).
- **`leansplit.py`** splits a module.
- **`lake env lean --run scripts/refactor/PrintConst.lean <Module> <Name>…`** prints the type and
  value of each named constant, which helps to read a diff.

The Python tools print their usage with `--help`. Lean realizes equation lemmas lazily, so a pure
move can change the module that an `.eq_1` lemma is recorded in. That is one reason the diff
ignores modules.

## Local records

- **`questions.md`** is ignored by Git. Keep local uncertainties and suspected upstream defects in
  it.
- **Confirmed regressions and public limitations** go into tracked tests and docs.
- **Temporary files.** Delete temporary proof checks and logs once their results are recorded.
- **Build outputs.** Never edit Lake's build outputs by hand.
