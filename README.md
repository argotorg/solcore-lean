# solcore-lean

An executable specification of Solcore in Lean 4, tested against the Rust compiler
[solcore-rs](https://github.com/argotorg/solcore-rs).

The project has four parts:

- a **source frontend**, which parses and type-checks Solcore and compiles it to Core;
- **Core**, a typed intermediate language with an evaluator and a machine that runs with a step
  budget and can resume from a checkpoint;
- a **contract runtime**, which models accounts, storage, calls, and transaction commits and
  rollbacks;
- an **importer** for the Hull code that solcore-rs produces, so that its output runs on Core.

What is proved is summarized under [Proof status](#proof-status). How the Lean and Rust pipelines
are compared is under [Differential testing](#differential-testing).

## Build and test

Use Lean and Lake at the version in [lean-toolchain](lean-toolchain). From the repository root:

```sh
lake build
lake test
node scripts/check-kernel.mjs
```

Node.js is needed for the kernel check. Lean warnings are treated as errors.

## Using the frontend

The compiler is a Lean library:

```lean
import Solcore.Frontend.SourceCompiler
```

A small source program:

```text
function main() returns (Word) {
  return 55;
}
```

Source files are passed as a `Workspace.RawWorkspace`. The
[execution tests](Solcore/Test/SourceSemantics/CoreLowering/Foundations/Execution.lean) show how to
compile a workspace, open a session, call an entry point, and resume when the fuel runs out. The
[runtime API overview](docs/design/core-runtime-unification.md#public-runtime-api) describes values,
handles, snapshots and execution options.

The language follows the pinned solcore-rs for its checked integer types, `unchecked` blocks,
shifts, memory arrays and slices, and closures that capture by value. The
[source semantics guide](docs/guide/source-semantics.md) describes the semantics. The
[roadmap](docs/design/next-implementation-roadmap.md) says what is still missing and links the
design notes that record the differences from upstream.

## Running solcore-rs output

The [Rust Hull importer](Solcore/Frontend/RustHull/) accepts typed Hull output from solcore-rs at
commit `e2eef19409fc8879cd4a9cc342ed60e3152f72c0`. It checks the imported annotations, translates
Hull and inline Yul into Core, and checks the result before running it.

- **Supported:** all 81 standard opcode wrappers, constructors, dynamic ABI values, byte memory,
  storage, logs and calls between imported accounts.
  - CREATE, CREATE2 and SELFDESTRUCT update an explicit account world.
  - Keccak, SHA-256, RIPEMD-160, ECRECOVER and P256 verification run in Core.
  - Linked Sonatina code images supply observable code bytes.
  - EVM gas is not metered: Core fuel counts transitions instead.
- **Library:** `import Solcore.Frontend.RustHull`.
  - The entry points are `RustHull.decodeText`, `RustHull.ScalarExecution.prepare`,
    `RustHull.LinkedContract.prepareDeployment` and `RustHull.Contract.runWithReceipt`.
  - [RustHullScenarioRun.lean](Tests/RustHullScenarioRun.lean) shows deployment and sequential
    calls.
- **Export scripts.** These need a checkout of the pinned revision; each has `--help`.
  - [export-rust-hull.py](scripts/export-rust-hull.py) exports checked Hull.
  - [export-rust-code-image.py](scripts/export-rust-code-image.py) exports linked code images.
  - [rust-scenario-parity.py](scripts/rust-scenario-parity.py) runs the fixtures' constructor
    and call scenarios.
- **Parity:** the checked Rust driver accepts all 182 fixtures of the pinned contract inventory,
  and their 1,699 constructor and call observations match the fixture expectations on Core.
  [RUST_PARITY.md](scripts/RUST_PARITY.md) lists the gates and how to reproduce them.

Importing Rust Hull does not prove the Rust compiler correct, and it does not extend the native
Lean source checker to every Rust feature. Recursive references use the Rust backends' Word
layout, and aggregate cases that fail in both backends stay errors. Arbitrary EVM bytecode and
other precompiles are outside the executable code catalogue.

## Proof status

Core has proofs of type preservation and finite execution safety. The
independent source semantics also has a type preservation proof. Correspondence
between native source execution and generated Core code has been proved for
parts of the language; the theorem covering the complete compiler remains
unfinished. The [Core runtime unification design](docs/design/core-runtime-unification.md)
records that work.

`import Solcore.Frontend.RustHull.Safety` provides safety proofs for imported
Hull. Successful preparation supplies the typing conditions for input parsing,
contract initialization, execution and checkpoint resumption. These proofs
exclude Core machine faults while allowing language failures, reverts and
exhausted fuel budgets.

The separate [Hull meaning-preservation proofs](docs/design/hull-meaning-preservation.md)
connect independent finite Hull evaluations to actual lowering and public
execution, including repeated resumptions. Connected features include recursive
functions, loops, language faults, memory, storage, logs, return data, all four
message-call modes, root reentry and account destruction. Contract creation,
precompile execution, independent assembly semantics and object linking still
need their full public meaning-preservation connections. Executable support is
broader than this proved subset.

The native source compiler handles closed entry points with a finite
specialization plan. Its source contract members, persistent storage and
external calls have yet to be connected to `ContractRuntime`; its ABI wrapper
is limited to static Word values. The Rust Hull path has a separate import
boundary and supports generated dynamic ABI code.

## Differential testing

Generated programs run on three paths, and the results are compared:

1. **The original generated Core program.** This is the reference.
2. **EVM bytecode from the pinned Rust compiler.** It is built through Sonatina at O0 (the
   default) or O2, or through Yul and solc.
3. **The Rust compiler's Hull**, imported and run on Lean's Core.

Agreement in a corpus is evidence, not proof. Generated programs pass the Core checker, and a
separate [source emitter theorem](docs/design/scalar-emitter-meaning.md) connects the text of
fifteen source emitters to Core, under an independent source semantics and a stated Rust-pipeline
boundary. Closed programs may be constant-folded, so source coverage is not runtime opcode
coverage.

- **Profiles.** The default suite has 66 profiles.
  - The 34 pure ones cover Word expressions, raw primitives, inline Yul, call graphs, loops,
    recursion, aggregates, generic functions, enums, traits, memory values, revert data, halts,
    checked integer arithmetic and shifts, memory arrays, and closures.
  - The 32 stateful ones cover storage, loops over storage, calls between contracts, logs, call
    value, dynamic ABI values, mappings, malformed calldata, several methods, returned values,
    constructor arguments, and return data across calls.
  - Yul can run every pure profile and 30 of the stateful ones.
  - [SEMANTIC_DIFFERENTIAL.md](scripts/SEMANTIC_DIFFERENTIAL.md) gives each profile's generator,
    reference and results.
- **Runners.**
  - A single-case runner saves all three observations and replays them strictly.
  - A campaign runner reduces failures and keeps their classification.
  - [semantic-suite.py](scripts/semantic-suite.py) runs the fixed and random suites under shared
    time and disk limits.
  - [semantic-fuzz.py](scripts/semantic-fuzz.py) repeats random suites with advancing seeds. It
    counts findings by signature, so that upstream defects already recorded count as known
    rather than new.
  - [SEMANTIC_CI.md](scripts/SEMANTIC_CI.md) explains how to prepare and run them.
- **Pinned fixtures.** [semantic-fixtures.py](scripts/semantic-fixtures.py) runs the recorded steps
  of solcore-rs's own end-to-end fixtures on Hull, O0, O2 and Yul. It also runs mutants of their
  inputs, call sequences and sources. These fixtures have no original Core, so only the compiled
  paths are compared; all 1,699 recorded steps agree on every path.
- **CI.** The [workflow](.github/workflows/semantic.yml) runs the fixed corpora and recorded random
  seeds. Its automatic triggers are disabled, so it runs only on manual dispatch.

The [differential-testing guide](docs/guide/differential-testing.md) explains the comparison model
and how to read a disagreement.

## Code layout

Each area has an umbrella module, a short front with the specification and main theorems, and an
`Internal/` directory with the rest. The [developer guide](docs/guide/README.md) has a page per
area: where things are, which definitions and theorems other code builds on, and how to make and
test a change. Its [conventions](docs/guide/conventions.md) and [workflow](docs/guide/workflow.md)
pages apply to every area.

| Module | Contents | Guide |
| --- | --- | --- |
| [Syntax](Solcore/Syntax.lean) | AST, lexer, parser, and parser proofs. | [Syntax](docs/guide/syntax.md) |
| [TypeSystem](Solcore/TypeSystem.lean) | Types, substitutions, unification, and inference. | [Foundations](docs/guide/foundations.md) |
| [Frontend.Current](Solcore/Frontend/Current.lean) | Source checking, staging, specialization, and compilation to Core. | [Frontend](docs/guide/frontend.md) |
| [Frontend/RustHull](Solcore/Frontend/RustHull/) | Checked Rust Hull import, contract effects and Core execution. | [Frontend](docs/guide/frontend.md) |
| [Core](Solcore/Core.lean) | Typed syntax, mutable cells, evaluator, execution machines, and safety proofs. | [Core](docs/guide/core.md) |
| [SourceSemantics](Solcore/SourceSemantics.lean) | Independent source semantics and type preservation proofs. | [Source semantics](docs/guide/source-semantics.md) |
| [ContractRuntime](Solcore/ContractRuntime.lean) | Accounts, world state, host effects, calls, and transactions. | [ContractRuntime](docs/guide/contract-runtime.md) |
| [Abi](Solcore/Abi.lean) / [Core.Wire](Solcore/Core/Wire.lean) | ABI encoding and the JSON representation of Core. | [Foundations](docs/guide/foundations.md), [Core](docs/guide/core.md) |
| [Synthesis.Core](Solcore/Synthesis/Core.lean) | Checked program generation and shrinking for bounded execution profiles. | [Synthesis](docs/guide/synthesis.md) |
| [Test](Solcore/Test/) | Tests and reusable fixtures, registered in [Tests/Main.lean](Tests/Main.lean). | [Tests](docs/guide/tests.md) |

[Solcore.lean](Solcore.lean) provides the main import. The source-to-Core correspondence proofs
live under [SourceSemantics/CoreLowering](Solcore/SourceSemantics/CoreLowering.lean); their guide is
[Core lowering](docs/guide/core-lowering.md).

## Contributing

Definitions and proofs live under `Solcore/`. Put tests under `Solcore/Test/` and register them in
`Tests/Main.lean`. Run the build, tests and kernel check above before submitting changes.
[Workflow](docs/guide/workflow.md) lists every check CI runs, and
[Conventions](docs/guide/conventions.md) says where new code goes.

The [kernel check](scripts/check-kernel.mjs) rejects the words `sorry`, `axiom`, `partial`,
`unsafe` and a few others anywhere in the semantic modules, comments included.
