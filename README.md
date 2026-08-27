# solcore-lean

solcore-lean is an executable formal specification of Solcore written in
Lean 4. It is an independent reference implementation: neither the Haskell
compiler nor the Rust compiler defines the language.

The repository currently provides:

- a versioned command-line Oracle for checking and evaluating Semantic Core
  programs;
- a versioned command-line Oracle for parsing the supported single-file
  Solcore syntax;
- Lean definitions for the language rules and executable procedures; and
- machine-checked proofs connecting those procedures to the rules.

The source parser is intentionally separate from the Semantic Core evaluator.
Parsing a source file does not resolve imports or names, check source types,
run a contract, or elaborate the file into Semantic Core.

## Requirements

- Lean 4.32.1, selected by the checked-in lean-toolchain file
- Lake, distributed with Lean
- Node.js, used by repository validation scripts

## Build and test

From the repository root:

    lake build
    lake test
    node scripts/verify-metadata.mjs
    node scripts/check-kernel.mjs

## Run the Oracle

Build and inspect the command-line interface:

    lake exe solcoreOracle --help

The two current public interfaces are:

| Command | Purpose |
| --- | --- |
| capabilities-v3 | Describe Semantic Core v2 checking and evaluation |
| capabilities-v4 | Describe Surface v1 single-file parsing |

The Oracle reads newline-delimited JSON from standard input when no command is
given. Each request produces exactly one response in the same order.

    lake exe solcoreOracle < Tests/golden/m1c-eval-operations-request.ndjson
    lake exe solcoreOracle < Tests/golden/m2b-parse-outcomes-request.ndjson

Useful example requests:

- [Core checking](Tests/golden/m1c-check-rejected-request.ndjson)
- [Core evaluation](Tests/golden/m1c-eval-operations-request.ndjson)
- [Surface parsing](Tests/golden/m2b-parse-outcomes-request.ndjson)
- [Mixed protocol versions](Tests/golden/mixed-v1-v2-v3-v4-request.ndjson)

Requests must contain one compact JSON object per line. Malformed envelopes,
unknown schemas, and invalid field shapes produce protocol errors rather than
language results.

## Use as a Lean library

Import the public umbrella module:

    import Solcore

Or import an individual layer:

    import Solcore.Core
    import Solcore.Surface
    import Solcore.Workspace

## Public schemas

- [Oracle v3](schema/oracle-v3.schema.json)
- [Oracle v4](schema/oracle-v4.schema.json)
- [Semantic Core v2](schema/semantic-core-v2.schema.json)
- [Surface v1](schema/surface-v1.schema.json)
- [Parse result v1](schema/parse-result-v1.schema.json)

The [documentation guide](docs/README.md) explains the specification,
architecture, supported features, and development process.
