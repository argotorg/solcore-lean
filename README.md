# solcore-lean

`solcore-lean` is an executable formal specification of Solcore written in
Lean 4. The Lean definitions and theorems in this repository are the
specification; the Haskell and Rust implementations are comparison evidence,
not language authorities.

The repository currently provides:

- a canonical source lexer, parser, recovery model, and source-preserving AST;
- workspace identity, module loading, resolution, type inference, trait
  selection, specialization, and restricted whole-program compilation;
- independent declarative source static, staging, and dynamic semantics;
- a checked Semantic Core with executable checking and evaluation, machines,
  fuel properties, and safety/correspondence proofs;
- checked-Core contract execution over explicit world and transaction state;
- static-word ABI encoding and Keccak-256 support; and
- reproducible generation and shrinking of a checked pure Core fragment.

The public interfaces are Lean modules. Import the smallest umbrella that owns
the behavior you need:

| Area | Import |
| --- | --- |
| Complete library | `Solcore` |
| Canonical source syntax | `Solcore.Syntax` |
| Current whole-program frontend | `Solcore.Frontend.Current` |
| Declarative source semantics | `Solcore.SourceSemantics` |
| Semantic Core | `Solcore.Core` |
| Checked-contract execution | `Solcore.ContractRuntime` |
| ABI utilities | `Solcore.Abi` |
| Checked Core synthesis | `Solcore.Synthesis` |
| Generic representation utilities | `Solcore.Util` |

See the [architecture overview](docs/ARCHITECTURE.md),
[current status](docs/CURRENT_STATUS.md), and [project map](docs/PROJECT_MAP.md)
for the boundaries and known limitations of each layer.

## Requirements

- Lean 4.33.1, selected by the checked-in `lean-toolchain`
- Lake, distributed with Lean
- Node.js for the repository kernel-policy check

No separate Lean package installation step is required.

## Build and test

From the repository root:

```text
lake build
lake test
node scripts/check-kernel.mjs
```

Warnings are errors for the `Solcore` package. The Node.js check enforces the
semantic-kernel policy; it supplements rather than replaces the Lean build and
tests.

## Use as a Lean library

Import the complete public library:

```lean
import Solcore
```

Or parse canonical source directly:

```lean
import Solcore.Syntax

open Solcore.Syntax

def exampleSyntax : ParseResult :=
  Parser.parse {
    id := { origin := .main, path := "example.sol" }
    content := "type Store = mapping(address => word);"
  }
```

Successful parse results retain tokens, comments, lexical diagnostics, parse
diagnostics, and the source-preserving AST. Parsing alone does not establish
workspace validity, name resolution, or source typing; those responsibilities
belong to the workspace and frontend layers.

To use the current whole-program pipeline:

```lean
import Solcore.Frontend.Current
```

The caller supplies a raw workspace and an explicit root. The frontend checks
the workspace, resolves and types declarations, specializes the selected
entry, and chooses among the implemented execution backends. The exact input
and result types are exposed by the imported Lean modules; there is no
command-line protocol associated with this API.

To generate a reproducible checked Core program:

```lean
import Solcore.Synthesis

open Solcore.Synthesis.Core

def generatedNodeCount : Except GenerationError Nat := do
  let generated ← generate {
    seed := Seed.ofNat 0
    maxProgramNodes := 64
  }
  pure generated.nodeCount
```

`generate` returns a checker-sealed program in the supported pure Core
fragment. `shrink` returns checker-sealed candidates that are strictly smaller
under the library's size measure.

## Documentation

- [Documentation guide](docs/README.md)
- [Architecture](docs/ARCHITECTURE.md)
- [Current status and limitations](docs/CURRENT_STATUS.md)
- [Feature matrix](docs/FEATURE_MATRIX.md)
- [Semantic Core Wire](docs/CORE_WIRE.md)
- [Development guide](docs/DEVELOPMENT.md)
