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

## Running solcore-rs output

The [Rust Hull importer](Solcore/Frontend/RustHull/) accepts typed output from
`argotorg/solcore-rs` at commit `2a745e12974c373c3799fec81b48a53c7dce2ab4`.
It checks the imported annotations, translates Hull and inline Yul into Core,
and checks the resulting Core expression before execution.

This path supports all 81 standard opcode wrappers, contract constructors,
dynamic ABI values, byte memory, storage, logs, and calls between imported
accounts. CREATE/CREATE2 and SELFDESTRUCT update an explicit account world.
Keccak, SHA-256, RIPEMD-160, ECRECOVER and P256 verification execute in Core.
Exact linked Sonatina code images supply observable code bytes and object
offsets; execution uses the Core machine.

The export scripts require a checkout of the pinned Rust revision. They patch
only the isolated checkout supplied to `--upstream` and record source and tool
hashes beside each artifact. Run each script with `--help` for build and path
options:

- [export-rust-hull.py](scripts/export-rust-hull.py): checked Hull transport.
- [export-rust-code-image.py](scripts/export-rust-code-image.py): linked code images.
- [rust-scenario-parity.py](scripts/rust-scenario-parity.py): constructor and
  stateful execution against upstream fixture expectations.

Import the library with `import Solcore.Frontend.RustHull`. The entry points are
`RustHull.decodeText`, `RustHull.ScalarExecution.prepare`,
`RustHull.LinkedContract.prepareDeployment` and `RustHull.Contract.runWithReceipt`.
[RustHullScenarioRun.lean](Tests/RustHullScenarioRun.lean) shows artifact loading,
deployment, account balances and sequential calls. A context supplies account
state, transaction/block observations, and an optional gas value. Executable
code comes from a checked Hull catalogue with exact linked images. Core fuel
counts transitions; EVM gas consumption is not metered.

The pinned contract inventory covers 168 fixtures. The checked Rust driver
accepts 165; their 1,382 constructor and call observations match the fixture
expectations on Core. Three fixtures fail upstream source checks before export.
[RUST_PARITY.md](scripts/RUST_PARITY.md) lists the gates and how to reproduce them.

`import Solcore.Frontend.RustHull.Safety` provides the execution safety proofs.
Successful preparation supplies the typing conditions for actual input parsing,
contract initialization, execution and checkpoint resumption. A Core machine
fault is excluded; a language failure, revert or exhausted fuel budget remains
a possible result.

Importing Rust Hull does not prove the Rust compiler correct or extend the
native Lean source checker to every Rust feature. Recursive references use the
Rust backends’ Word layout; aggregate construction and unfolding cases that fail
in both backends remain explicit errors. Arbitrary EVM bytecode and additional
precompiles are outside the executable code catalogue. Compatibility decisions,
coverage, and unresolved upstream issues are recorded in
[questions.md](questions.md).

## Code layout

| Module | Contents |
| --- | --- |
| [Syntax](Solcore/Syntax.lean) | AST, lexer, parser, and parser proofs. |
| [TypeSystem](Solcore/TypeSystem.lean) | Types, substitutions, unification, and inference. |
| [Frontend.Current](Solcore/Frontend/Current.lean) | Source checking, staging, specialization, and compilation to Core. |
| [Frontend/RustHull](Solcore/Frontend/RustHull/) | Checked Rust Hull import, contract effects and Core execution. |
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

The native source compiler handles closed entry points with a finite
specialization plan. Its source contract members, persistent storage and
external calls have yet to be connected to `ContractRuntime`; its ABI wrapper
is limited to static Word values. The Rust Hull execution path above has a
separate import boundary and supports generated dynamic ABI code.

The [Core runtime unification design](docs/design/core-runtime-unification.md)
records the compiler design and the remaining proof work.

## Contributing

Definitions and proofs live under `Solcore/`. Put tests under `Solcore/Test/`
and register them in `Tests/Main.lean`. Run the build, tests, and kernel check
above before submitting changes.

The [kernel check](scripts/check-kernel.mjs) rejects declarations such as
`sorry`, `axiom`, `partial`, and `unsafe` in semantic modules.
