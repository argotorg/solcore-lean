# solcore-lean

`solcore-lean` is an executable formal specification of Solcore written in
Lean 4. It provides an independent reference implementation for testing Solcore
parsers and semantics without treating either the Haskell or Rust compiler as
the definition of the language.

The repository can currently:

- parse the supported single-file Solcore syntax and return a structured AST
  or source diagnostic;
- type-check and evaluate self-contained programs encoded in the project's
  small, typed Semantic Core format; and
- expose those operations through a versioned, line-oriented JSON command-line
  interface.

The implementation is accompanied by declarative rules and machine-checked
proofs connecting those rules to the executable code.

## Supported interfaces

| Interface | Use it for | Input |
| --- | --- | --- |
| Oracle v3 | Type-checking and evaluating Semantic Core | `solcore-semantic-core/v2` JSON under profile `core-m1c-v1` |
| Oracle v4 | Parsing one Solcore source file | Source text plus a file label, under profile `frontend-m2b-v1` |

Oracle v4 is a parser, not a complete compiler. It does not resolve imports or
names, type-check source programs, elaborate source into Semantic Core, or run
contracts. Oracle v1 and v2 remain available for compatibility with their
older schemas.

## Requirements

- Lean `v4.32.1`, selected automatically by the checked-in `lean-toolchain`
- Lake, included with Lean
- Node.js, for metadata and source-policy checks

## Build and test

From the repository root:

```sh
lake build
lake test
```

To run the repository checks used alongside the Lean build:

```sh
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
```

## Run the Oracle

Build and run the command-line executable with Lake:

```sh
lake exe solcoreOracle --help
```

Inspect the supported contracts and limits:

```sh
lake exe solcoreOracle capabilities-v3
lake exe solcoreOracle capabilities-v4
```

With no arguments, the Oracle reads newline-delimited JSON (NDJSON) from
standard input. Each input line produces exactly one output line, in the same
order:

```sh
lake exe solcoreOracle < Tests/golden/m1c-eval-operations-request.ndjson
lake exe solcoreOracle < Tests/golden/m2b-parse-outcomes-request.ndjson
```

Each request identifies its protocol with the `schema` field. These checked-in
examples are useful starting points for custom clients:

- [Semantic Core checking request](Tests/golden/m1c-check-rejected-request.ndjson)
- [Semantic Core evaluation requests](Tests/golden/m1c-eval-operations-request.ndjson)
- [Surface parser requests](Tests/golden/m2b-parse-outcomes-request.ndjson)
- [Mixed-version request stream](Tests/golden/mixed-v1-v2-v3-v4-request.ndjson)

Requests must contain one compact JSON object per line. Malformed envelopes,
unknown schemas, and invalid field shapes produce a protocol error rather than
a language result.

## Use it as a Lean library

Import the main module to use the Solcore definitions and Oracle APIs from
Lean:

```lean
import Solcore
```

Individual layers can also be imported directly:

```lean
import Solcore.Core
import Solcore.Surface
import Solcore.Workspace
```

## Schemas and documentation

- [Documentation guide](docs/README.md)
- [Specification charter](docs/SPEC_CHARTER.md)
- [Feature matrix](docs/FEATURE_MATRIX.md)
- [Oracle v3 schema](schema/oracle-v3.schema.json)
- [Oracle v4 schema](schema/oracle-v4.schema.json)
- [Semantic Core v2 schema](schema/semantic-core-v2.schema.json)
- [Surface v1 schema](schema/surface-v1.schema.json)
- [Parse result v1 schema](schema/parse-result-v1.schema.json)
