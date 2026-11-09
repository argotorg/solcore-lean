# Differential testing

The differential tests compare Lean's meaning of generated programs with what the pinned Rust
compiler, `argotorg/solcore-rs`, produces for them. They cover a bounded, gas-independent part of
the language.

- README's [Differential testing](../../README.md#differential-testing) section lists what is
  covered.
- The [roadmap](../design/next-implementation-roadmap.md) records the status and the order of
  further work.

## The three observations

Each generated case is observed three ways:

1. **Direct Core.** Lean executes the original generated Core program.
2. **Rust EVM.**
   - The case is emitted as a `.sol` source.
   - The checked Rust frontend and a backend compile it. The backend is Sonatina O0, Sonatina O2,
     or Yul through solc.
   - The bytecode runs on the pinned EVM (Anvil).
3. **Imported Hull.** The same source's checked Rust Hull is imported into Lean and run on Core.

Direct Core against Rust EVM is the primary comparison. Imported Hull helps to localize a
difference:
- If both Rust-derived paths agree against direct Core, look at the emitter or the shared Rust
  frontend.
- If direct Core and imported Hull agree against the EVM, look at the backend, the EVM setup or the
  observation adapter.

These are triage hints, not proofs of which component is wrong.

**What else to know about the comparison:**
- **The emitter is trusted.** It is part of the test setup until its correspondence is proved.
  [Source emitter meaning](../design/scalar-emitter-meaning.md) covers the emitters proved so far.
- **Stateful profiles observe more than a return value.** They compare committed storage and,
  depending on the profile, balances, logs and return data.
- **The pinned end-to-end fixtures** compare the compiled paths with each other, without a Core
  reference.

## Where things are

| Part | Where |
| --- | --- |
| Generators, plans and emitters | [`Solcore/Synthesis`](../../Solcore/Synthesis.lean); see [Synthesis](synthesis.md) |
| Case tools and Hull runners | Lean executables in `Tests/`, each a `lean_exe` in [`lakefile.lean`](../../lakefile.lean) |
| Runners, campaigns, suites and the fuzz driver | `scripts/semantic-*.py` |
| Fixed corpora | `scripts/semantic-*-corpus.json`, validated by `Tests/scripts/test-semantic-*-corpus.py` |
| Rust exporters and the pinned tools | `scripts/export-rust-*.py`, `scripts/*.rs` and `scripts/prepare-semantic-tools.py`, built under `.upstream/` |
| Fixed parity inventories | [`scripts/RUST_PARITY.md`](../../scripts/RUST_PARITY.md) |

Two guides in `scripts/` go into detail:
- [`scripts/SEMANTIC_DIFFERENTIAL.md`](../../scripts/SEMANTIC_DIFFERENTIAL.md) documents every
  profile, runner and recorded finding.
- [`scripts/SEMANTIC_CI.md`](../../scripts/SEMANTIC_CI.md) documents the suites, the CI workflow and
  continuous fuzzing.

## Rules

- **The reference is pinned.**
  - solcore-rs is pinned at a fixed revision, given at the top of `scripts/SEMANTIC_DIFFERENTIAL.md`.
  - The backend, the standard library, solc and the EVM are pinned too.
  - Moving the pin is a separate, explicit change.
- **Lean follows upstream's semantics at the pin.**
  - When a change touches a construct whose behaviour could differ, its design note records a probe
    of the pinned Rust paths.
  - Where Lean decides to stay different, the affected programs are not comparison cases. For
    example, Lean faults on a read of an uninitialized local, where solcore-rs reads zero (see
    [Source semantics](source-semantics.md#closures-capture-by-value)).
- **Keep the reference independent.** The main comparison must not share the Rust frontend with its
  reference computation.
- **Do not hide failures.**
  - Never suppress a failing generated case, and never turn a compiler failure into a successful
    comparison.
  - The fuzz driver counts recorded upstream findings as known, by their stable signatures.
- **Do not overclaim.**
  - Do not label an unexplained difference as a confirmed upstream bug.
  - Record a suspected upstream defect in the local, ignored `questions.md`.
  - Put confirmed regressions in tracked tests and docs.
- **Keep limits separate.** Core fuel, EVM gas and process timeouts are separate resource limits.
- **Report exactly.**
  - Report a run by its counts per profile and backend, known findings included.
  - Freeze the scripts and tools while a run is in progress.

## Adding a profile

[Synthesis](synthesis.md) has the checklist: the plan and the emitter, the case tool, the corpus,
the runner registration and the docs.
