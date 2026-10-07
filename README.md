# solcore-lean

An executable specification of Solcore in Lean 4.

The project includes a source frontend, a typed intermediate language (Core),
and a model of contract execution. Source programs compile to Core. Its evaluator
takes a fuel budget that limits the number of execution steps. The contract
runtime models accounts, storage, calls, and transaction commits and rollbacks.

## Build and test

Use Lean and Lake with the version pinned in [lean-toolchain](lean-toolchain).
From the repository root:

```sh
lake build
lake test
node scripts/check-kernel.mjs
```

Node.js is needed for the kernel check. Lean warnings are treated as errors.

## Using the frontend

The compiler is a Lean library. Import its public API with:

```lean
import Solcore.Frontend.SourceCompiler
```

A small source program:

```text
function main() returns (Word) {
  return 55;
}
```

Source files are supplied as a `Workspace.RawWorkspace`. The
[execution tests](Solcore/Test/SourceCoreExecution.lean) show how to compile a
workspace, open a session, call an entry point, and resume after the fuel runs
out. They also cover recursive functions, closures with mutable captures, and
mappings. See the [API guide](docs/design/core-runtime-unification-api.md) for
values, handles, snapshots, and execution options.

## Code layout

| Module | Contents |
| --- | --- |
| [Syntax](Solcore/Syntax.lean) | AST, lexer, parser, and parser proofs. |
| [TypeSystem](Solcore/TypeSystem.lean) | Types, substitutions, unification, and inference. |
| [Frontend.Current](Solcore/Frontend/Current.lean) | Source checking, staging, specialization, and compilation to Core. |
| [Core](Solcore/Core.lean) | Typed syntax, mutable cells, evaluator, execution machines, and safety proofs. |
| [SourceSemantics](Solcore/SourceSemantics.lean) | Independent source semantics and type preservation proofs. |
| [ContractRuntime](Solcore/ContractRuntime.lean) | Accounts, world state, host effects, calls, and transactions. |
| [Abi](Solcore/Abi.lean) / [Core.Wire](Solcore/Core/Wire.lean) | ABI encoding and the JSON representation of Core. |
| [Test](Solcore/Test/) | Tests and reusable fixtures, registered in [Tests/Main.lean](Tests/Main.lean). |

[Solcore.lean](Solcore.lean) provides the main import. The source-to-Core
correspondence proofs live under
[SourceSemantics/CoreLowering](Solcore/SourceSemantics/CoreLowering.lean).

## Status

Development is ongoing. Core has proofs of type preservation and finite
execution safety. The independent source semantics also has a type preservation
proof. Correspondence between source execution and generated Core code has
been proved for parts of the language; the theorem covering the complete
compiler is still in progress.

Compilation currently handles closed entry points with a finite specialization
plan. Source contract members, persistent storage, and external calls have yet
to be connected to `ContractRuntime`. ABI support is limited to static Word
values.

The [Core runtime unification design](docs/design/core-runtime-unification.md)
records the compiler design and the remaining proof work.

## Contributing

Definitions and proofs live under `Solcore/`. Put tests under `Solcore/Test/`
and register them in `Tests/Main.lean`. Run the build, tests, and kernel check
above before submitting changes.

The [kernel check](scripts/check-kernel.mjs) rejects declarations such as
`sorry`, `axiom`, `partial`, and `unsafe` in semantic modules.
