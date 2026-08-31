# solcore-lean

`solcore-lean` is an executable formal specification of Solcore written in
Lean 4. It provides an independent reference model for checking programs and
running their semantics; neither the Haskell compiler nor the Rust compiler is
treated as the language definition.

The repository provides:

- a checked Semantic Core language with executable typing and evaluation;
- Oracle v5 execution of checked contracts from an explicit initial world;
- commit on return and rollback on balance-preflight rejection, revert, or trap;
- observable state, return data, logs, balances, and contract creation;
- reproducible generation and shrinking of a checked, pure Core v3 subset;
- versioned compatibility interfaces for previously published formats; and
- Lean proofs and executable tests for the modeled rules.

Oracle v5 consumes Semantic Core rather than source text. The canonical source
lexer and parser are available as a Lean library and cover complete files,
declarations, types, expressions, patterns, statements, inline Yul, comments,
diagnostics, and recovery. Name resolution, source type checking, elaboration,
and end-to-end source execution are not yet implemented.

## Requirements

- Lean 4.32.1, selected by the checked-in `lean-toolchain` file
- Lake, distributed with Lean
- Node.js, used by repository validation scripts

Clone the repository, enter its root directory, and let Lake use the pinned
Lean toolchain. No separate package installation step is required.

## Build and test

Run the complete local validation suite from the repository root:

```text
lake build
lake test
node scripts/verify-metadata.mjs
node scripts/check-kernel.mjs
```

Build and inspect the command-line Oracle with:

```text
lake exe solcoreOracle --help
```

## Query Oracle v5

The simplest way to inspect the checked-contract interface is its capability
report:

```text
lake exe solcoreOracle capabilities-v5
```

The report identifies the exact Oracle, Core, specification, and profile
versions; supported queries and contract profiles; observation kinds; and
default resource limits.

Without a command, the executable reads newline-delimited JSON from standard
input. Each input line produces exactly one output line in the same order.
This is a complete minimal Oracle v5 capabilities request:

```json
{"schema":"solcore-oracle/v5","id":"readme-v5","spec":"solcore/0.1.0-draft.5","profile":{"id":"contract-m3a-v1","digest":"sha256:da3d49b830d25705634cfda568691f1f12fe5a7d038bd0b7ca5839134c1073d5"},"limits":{"jsonDepth":2048,"jsonNodes":2000000,"coreDepth":1024,"coreNodes":1000000,"scenarioEntries":100000,"identifierBytes":256,"calldataBytes":1048576,"evaluationSteps":1000000},"query":{"kind":"capabilities"}}
```

Save that single line as `request.ndjson`, then run:

```text
lake exe solcoreOracle < request.ndjson
```

Oracle v5 also accepts `coreCheck` and `execute` queries. Execution requests
include contract definitions expressed as Core Wire v3 programs, initial
accounts and storage, nested-call and creation configuration, invocation data,
fuel, and the state probes to return. Oracle v5 checks and admits those contract
definitions before execution. Malformed JSON and invalid wire values produce
protocol errors; well-formed programs that fail checking or admission produce
typed rejections.

Run the checked-in execution example directly with:

```text
lake exe solcoreOracle < Tests/golden/v5-execute-request.ndjson
```

Older capability reports remain available through `capabilities`,
`capabilities-v2`, `capabilities-v3`, and `capabilities-v4`.

## Use as a Lean library

Import the complete public library:

```lean
import Solcore
```

Or import the checked-contract Oracle directly:

```lean
import Solcore.Oracle.V5
```

To lex and parse canonical Solcore source:

```lean
import Solcore.Syntax

open Solcore.Syntax

def exampleSyntax : ParseResult :=
  Parser.parse {
    id := { origin := .main, path := "example.sol" }
    content := "type Store = mapping(address => word);"
  }
```

Successful results retain tokens, comments, lexical diagnostics, parse
diagnostics, and a source-preserving AST for the complete canonical grammar.
Ordinary malformed input is reported in those diagnostic lists; the
exceptional branch is reserved for an internal executor invariant.

To generate a reproducible checked Core program, import the synthesis library:

```lean
import Solcore.Synthesis

open Solcore.Synthesis.CoreV3

def generatedNodeCount : Except GenerationError Nat := do
  let generated ← generate {
    seed := Seed.ofNat 0
    maxProgramNodes := 64
  }
  pure generated.nodeCount
```

`make` packages the same generated program as a minimal Oracle v5 execution
case. `shrink` returns only checker-sealed, strictly smaller candidates. The
generator targets Semantic Core directly and does not parse Solcore source.

## Protocol documentation

- [Oracle v5 request, response, and execution catalog](docs/ORACLE_V5_WIRE.md)
- [Semantic Core Wire v3 catalog](docs/CORE_WIRE_V3.md)
- [Current supported scope and limitations](docs/CURRENT_STATUS.md)
- [Documentation guide](docs/README.md)
