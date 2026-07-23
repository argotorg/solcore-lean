# solcore-lean

`solcore-lean` is a Lean 4 project for building an executable formal
specification of the Solcore language and a reference implementation for semantic
differential fuzzing.

The project is currently at **M0 (freezing the specification boundary and
execution contract)**. The language semantics themselves have not yet been
implemented. This phase establishes the specification authority, version and
profile, comparison baselines, standard-library content, Oracle protocol, verdict
categories, and unresolved decisions in a machine-checkable form.

## What M0 fixes

- Exact pin of Lean `v4.32.1`
- draft language version `solcore/0.1.0-draft.1`
- canonical core profile `core-v1`
  - Canonical solver policy is `tabled`
  - M0 has no language feature with complete normative semantics
  - The Core profile does not include an EVM revision
  - UTF-8 byte spans
  - Value observations without gas
  - canonical Lean JSON digest
    `sha256:2ccae018d736fa61910a6c2475fe3088bad2e924b60d43a9748852b7cc817ec8`
- upstream Haskell baseline
  `1d490d8bb5f374356f06e0720655496482eb1fb4`
- comparison Rust baseline
  `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`
- Revision, byte size, SHA-256, and fileset digest for the six upstream
  standard-library files
- NDJSON request/response contract for `solcore-oracle/v1`
- `accepted / rejected / unsupported / inconclusive / executed / internalError`
  verdicts separated from protocol errors

Haskell and Rust implementation defaults are not part of the specification.
They are isolated in [`Solcore/Baseline.lean`](Solcore/Baseline.lean) as
evidence for differential investigation.

## Running

```sh
lake --wfail build
lake --wfail test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
lake exe solcoreOracle --help
lake exe solcoreOracle --version
lake exe solcoreOracle capabilities
```

To verify the raw bytes of the canonical standard library, run
`node scripts/verify-metadata.mjs --canonical-source-root <solcore>/std`
against the pinned upstream checkout. CI requires this verification.

When invoked without arguments, the Oracle reads one NDJSON request per line from
standard input and returns one response per line in the same order. At M0,
`capabilities` is the only successful query. All other known queries return
`unsupported`.

## Specification documents

- [Specification charter](docs/SPEC_CHARTER.md)
- [Feature matrix](docs/FEATURE_MATRIX.md)
- [Compatibility matrix](docs/COMPATIBILITY_MATRIX.md)
- [M1 Semantic Core plan](docs/M1_PLAN.md)
- [Architecture decision records](docs/adr)
- [Checked-in core profile](profiles/solcore-0.1.0-draft.1-core.json)
- [Oracle JSON Schema](schema/oracle-v1.schema.json)

## Implementation roadmap

1. **M0 — contract:** version/profile, ADRs, baselines, Oracle schema, CI
2. **M1 — semantic core:** Core AST, typing relation, small-step/CEK semantics,
   executable evaluator, correspondence theorems
3. **M2 — frontend:** parser, name resolution, elaboration,
   modules/type classes/comptime
4. **M3 — contracts:** ABI, storage, transaction observations
5. **M4 — differential fuzzing:** generator/shrinker, three-implementation
   comparison, regression corpus

A feature becomes `implemented` only when it has a declarative judgment, a
decision procedure, soundness and completeness connecting them (or an explicitly
documented one-way theorem), an Oracle observation, and conformance tests.
