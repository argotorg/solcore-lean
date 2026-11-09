# Developer guide

This guide is for people who change the code. It covers:
- how the repository is laid out, and where new code goes;
- which definitions and theorems other code relies on;
- how to make the common kinds of change, and how to check them.

README's [Proof status](../../README.md#proof-status) says what is proved. The design notes in
[`docs/design/`](../design/) describe work that is planned, under way or paused.

## Start here

| Page | Read it when |
| --- | --- |
| [Conventions](conventions.md) | Before your first change: how an area is laid out, where a declaration goes, the proof rules, and how to follow older notes |
| [Workflow](workflow.md) | To build, test and check a change, locally and as CI does |
| [Adding a language feature](adding-a-feature.md) | To take a source construct from the parser to the tests, through every layer |
| [Differential testing](differential-testing.md) | To work on the comparison with solcore-rs: the three paths, how to read a disagreement, the rules |

## Areas

A source program passes through these areas:
1. `Syntax` parses it.
2. `Frontend` compiles it.
3. It runs as Core, on `Core` and `ContractRuntime`.

Alongside that path:
- `SourceSemantics` gives source programs a meaning of their own.
- `SourceSemantics/CoreLowering` proves, for part of the language, that the compiled Core agrees
  with that meaning.
- `Frontend/RustHull` imports the Rust compiler's Hull IR and runs it on Core.
- `Synthesis` generates and emits the programs of the differential tests.

| Page | Code | What it does |
| --- | --- | --- |
| [Syntax](syntax.md) | `Solcore/Syntax` | AST, lexer and parser, with the parser proved against an independent grammar |
| [Foundations](foundations.md) | `Solcore/TypeSystem`, `Resolved`, `Workspace`, `Abi`, `Util` | Source types and inference, resolved expressions, the workspace kernel, the ABI layer |
| [Core](core.md) | `Solcore/Core` | The typed target language: syntax, typing, evaluator, machine, host requests and safety |
| [ContractRuntime](contract-runtime.md) | `Solcore/ContractRuntime` | Accounts, frames, transactions, nested calls and creation over checked Core |
| [Source semantics](source-semantics.md) | `Solcore/SourceSemantics` without `CoreLowering` | The independent semantics of source programs, and its type preservation |
| [Frontend](frontend.md) | `Solcore/Frontend` | The native compiler from source to Core, and the Rust Hull import |
| [Core lowering](core-lowering.md) | `Solcore/SourceSemantics/CoreLowering` | Proofs that compiled Core agrees with the source semantics |
| [Synthesis](synthesis.md) | `Solcore/Synthesis` | Program generators, source emitters and their meaning proofs |
| [Tests](tests.md) | `Solcore/Test`, `Tests` | Tests by subject, the test driver and the tool executables |

The areas are not strict layers. Some examples:
- The source semantics is stated over the frontend's typed IR (`Frontend/SourceInference`).
- The frontend's SourceCore lowering uses the semantics' capture binders.
- The Core wire codec uses a ContractRuntime scalar helper.

Check a file's imports before you assume that one area does not depend on another.

## Design notes

A design note is deleted once its work is done and its lasting content is in this guide or in
module docs. Git history keeps it.

| Note | Work |
| --- | --- |
| [Next implementation roadmap](../design/next-implementation-roadmap.md) | The order of testing and proof work, and the record of delivered units |
| [Integer types, `unchecked` blocks and shifts](../design/integer-types-unchecked-shifts.md) | The integer unit. Shifts and `unchecked` blocks without division are done; panics and the integer types are paused, with a resume point |
| [Core runtime unification](../design/core-runtime-unification.md) | The public runtime API, and what remains of the source-to-Core preservation theorem |
| [Hull meaning preservation](../design/hull-meaning-preservation.md) | The Hull import's meaning theorems and the remaining public connections |
| [Source emitter meaning](../design/scalar-emitter-meaning.md) | The emitters' meaning proofs, their assumptions, and the emitters still open |
