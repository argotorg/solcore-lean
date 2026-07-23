# solcore-lean

`solcore-lean` builds an executable formal specification of the Solcore language
and a reference implementation for semantic differential fuzzing in Lean 4.

The project is currently at **M1b (Semantic Core publication)**. It publishes the
closed Core implemented and proved in M1a—unit/bool/word literals, immutable
`let`, and conditionals—through strict Core JSON and the Oracle v2 `coreCheck`
and `coreEval` queries. The M0 language/profile and Oracle v1 remain frozen for
compatibility.

## What M0 fixes

- exact pin to Lean `v4.32.1`
- draft language version `solcore/0.1.0-draft.1`
- canonical Core profile `core-v1`
  - canonical solver policy is `tabled`
  - M0 enables no language feature whose normative semantics are complete
  - the Core profile does not include an EVM revision
  - UTF-8 byte spans
  - gas-free value observation
  - canonical Lean JSON digest
    `sha256:2ccae018d736fa61910a6c2475fe3088bad2e924b60d43a9748852b7cc817ec8`
- upstream Haskell baseline
  `1d490d8bb5f374356f06e0720655496482eb1fb4`
- comparison Rust baseline
  `38f4778ea461edfe59106bdb1f9f08c3307b0fc0`
- revision, byte size, SHA-256, and fileset digest for the six upstream standard
  library files
- NDJSON request/response contract for `solcore-oracle/v1`
- separation of `accepted / rejected / unsupported / inconclusive / executed /
  internalError` from protocol errors

## What M1a implements

- bounded word values represented by `Fin (2^256)`
- immutable lexical bindings represented by de Bruijn indices
- condition-first, selected-branch-only conditionals
- soundness and completeness of the executable checker with respect to
  declarative typing
- bidirectional correspondence between declarative big-step evaluation and the
  fuelled CEK machine
- transition determinism, progress, and preservation
- finite-fuel termination and machine-fault unreachability for well-typed
  closed programs

The detailed semantic choices are recorded in
[`ADR-0009`](docs/adr/0009-m1a-core-machine-and-evaluation-order.md).

## What M1b publishes

- the `solcore/0.1.0-draft.2` language version and `core-m1a-v1` profile
- five fine-grained normative features covering only the completed fragment
- the strict `solcore-semantic-core/v1` JSON codec
- canonical 256-bit words encoded as fixed-width lowercase hexadecimal
- deterministic type diagnostics with AST paths and structured arguments
- the `solcore-oracle/v2` `capabilities`, `coreCheck`, and `coreEval` queries
- distinct `inconclusive` outcomes for Core input limits and evaluation fuel
- mixed v1/v2 NDJSON streams and a canonical golden corpus

The publication boundary and v1 compatibility are recorded in
[`ADR-0010`](docs/adr/0010-m1b-core-wire-and-oracle-v2.md).

The Haskell and Rust implementation defaults are not specification authority.
They are isolated in [`Solcore/Baseline.lean`](Solcore/Baseline.lean) as evidence
for differential investigation.

## Running

```sh
lake --wfail build
lake --wfail test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
lake exe solcoreOracle --help
lake exe solcoreOracle --version
lake exe solcoreOracle capabilities
lake exe solcoreOracle capabilities-v2
```

To verify the raw bytes of the canonical standard library as well, run
`node scripts/verify-metadata.mjs --canonical-source-root <solcore>/std` against
the pinned upstream checkout. CI requires this verification.

When invoked without arguments, the Oracle reads one NDJSON request per line
from standard input and emits one response per line in the same order. In
Oracle v1, only `capabilities` succeeds; source-level queries remain
`unsupported`. In Oracle v2, `coreCheck` and `coreEval` are available for the
M1b profile's Semantic Core.

## Specification documents

- [Specification charter](docs/SPEC_CHARTER.md)
- [Feature matrix](docs/FEATURE_MATRIX.md)
- [Compatibility matrix](docs/COMPATIBILITY_MATRIX.md)
- [M1 Semantic Core plan](docs/M1_PLAN.md)
- [Architecture decision records](docs/adr)
- [Checked-in core profile](profiles/solcore-0.1.0-draft.1-core.json)
- [Checked-in M1b Core profile](profiles/solcore-0.1.0-draft.2-core-m1a.json)
- [Oracle v1 JSON Schema](schema/oracle-v1.schema.json)
- [Oracle v2 JSON Schema](schema/oracle-v2.schema.json)
- [Semantic Core JSON Schema](schema/semantic-core-v1.schema.json)

## Implementation roadmap

1. **M0 — contract:** version/profile, ADRs, baselines, Oracle schema, CI
2. **M1 — semantic core:** Core AST, typing relation, small-step/CEK semantics,
   executable evaluator, correspondence theorems
3. **M2 — frontend:** parser, name resolution, elaboration,
   modules/type classes/comptime
4. **M3 — contracts:** ABI, storage, transaction observation
5. **M4 — differential fuzzing:** generator/shrinker, three-implementation
   comparison, regression corpus

A feature becomes `implemented` only when it has a declarative judgment, a
decision procedure, a soundness/completeness theorem connecting them (or an
explicitly documented one-way theorem), an Oracle observation, and conformance
tests.
