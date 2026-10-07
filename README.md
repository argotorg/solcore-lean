# solcore-lean

Implemented behavior is defined by the Lean modules and checked by the
repository tests. This README keeps only a compact module guide and the
unfinished work.

## Module guide

External users should normally import an umbrella module instead of a leaf
implementation or proof module. The typical executable flow is
`Workspace / Syntax` → `Frontend.Current` (using `TypeSystem` and `Resolved`)
→ the common `SourceCompiler` / `SourceCoreExecution` API → `Core` execution.
`ContractRuntime` executes checked Core over accounts and world state; connecting
source contract members, persistent storage, and external calls is a later phase.
`SourceSemantics` is the independent, proof-facing specification of resolved
source programs.

| Module | Responsibility |
| --- | --- |
| [`Solcore`](Solcore.lean) | Main umbrella for the source frontend, declarative source semantics, Core, contract runtime, ABI, synthesis, workspace, and utilities. Optional boundaries such as Core Wire remain explicit imports. |
| [`Solcore.Spec`](Solcore/Spec.lean) | Pure umbrella for `Syntax`, `Core`, and `ContractRuntime`. It is not the complete frontend or complete source-semantics umbrella. |
| [`Solcore.Util`](Solcore/Util.lean) | Shared fixed-radix, fixed-width hexadecimal, and JSON helpers; it contains no language semantics. |
| [`Solcore.Workspace`](Solcore/Workspace.lean) | Canonical source/library identities and structural workspace validation. Module and name resolution happen later. |
| [`Solcore.Syntax`](Solcore/Syntax.lean) | Source-preserving AST, lexer, parser, diagnostics, declarative grammars, and parser correctness properties. |
| [`Solcore.Resolved`](Solcore/Resolved.lean) | Small already-resolved local-expression semantics with scope, typing, evaluation, renaming, lowering, and Core correspondence. It is not the whole-program name resolver. |
| [`Solcore.TypeSystem`](Solcore/TypeSystem.lean) | Source types, substitutions, first-order unification, rank-1 schemes, inference state, and their basic properties. |
| [`Solcore.Frontend.Current`](Solcore/Frontend/Current.lean) | Preferred executable whole-program entry: loading, resolution, inference, staging, specialization, linking, reusable compilation, root discovery, Core compilation, and execution through common artifacts, values, sessions, and checkpoints. |
| [`Solcore.Frontend`](Solcore/Frontend.lean) | Compatibility facade containing `Frontend.Current` and the older focused adapters under `Frontend.Fragments`. |
| [`Solcore.SourceSemantics`](Solcore/SourceSemantics.lean) | Algorithm-independent static, staging, dynamic, fault, and substitution judgments for resolved typed source, including constructive whole-language preservation for successful declarative executions. |
| [`Solcore.Core`](Solcore/Core.lean) | Typed Semantic Core syntax, stores, evaluator and machines, primitives, checker, runners, safety, and correspondence theorems. |
| [`Solcore.Core.Wire`](Solcore/Core/Wire.lean) | Canonical external Core representation, Core conversion, fixed host boundary, strict JSON codecs, and decode budgets. |
| [`Solcore.ContractRuntime`](Solcore/ContractRuntime.lean) | Checked-Core execution over accounts and world state: host effects, storage, frames, transactions, calls, creation, commit/rollback, and observations. |
| [`Solcore.Abi`](Solcore/Abi.lean) | Keccak-256 and the currently supported static-Word ABI codec and dispatch layer. |
| [`Solcore.Synthesis`](Solcore/Synthesis.lean) | Reproducible generation and shrinking of checker-accepted Semantic Core programs. |
| [`Solcore.Semantics`](Solcore/Semantics.lean) | Deprecated compatibility import for `Solcore.ContractRuntime`; new code should not use it. |

Umbrella files are the navigation and import boundaries for downstream code.
Leaf files, `*Properties` modules, parser grammar/trace units, and
`Frontend.Fragments` are focused implementation or proof units.

The independent source specification and executable Core safety have separate
proofs. [`WholeLanguagePreservation`](Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean)
is the constructive mutual preservation proof for declarative resolved-source
evaluation; [`ProgramEvaluates.preserves`](Solcore/SourceSemantics/Dynamic/Program.lean)
lifts it to the whole-program entry judgment.
[`SourceCompiler`](Solcore/Frontend/SourceCompiler.lean) reexports the common
[`SourceCoreExecution`](Solcore/Frontend/SourceCoreExecution.lean) API.
[`Core.BoundedSafety`](Solcore/Core/BoundedSafety.lean) proves finite Core
execution safety, while the public API authenticates inputs, heaps, code, and
handle ownership. The runtime typed-source evaluator has been removed.
Source-to-Core result and state correspondence is being developed under
[`CoreLowering`](Solcore/SourceSemantics/CoreLowering.lean); the complete public
compiler pipeline's meaning preservation proof remains unfinished.

## Contributor map

- Definitions and proofs live below `Solcore/`; place a proof close to the
  definition it establishes, usually in the adjacent `*Properties` module.
- Test modules and reusable fixtures live below `Solcore/Test/`.
  [`Tests/Main.lean`](Tests/Main.lean) imports the suites and registers their
  executable checks.
- Run `lake build`, `lake test`, and `node scripts/check-kernel.mjs` before
  submitting a change. Warnings are errors, and the kernel-policy check rejects
  proof escape hatches in semantic modules.
- The [Core runtime unification design](docs/design/core-runtime-unification.md)
  records the agreed migration scope, implementation tasks, and semantic
  preservation proof goals. Runtime unification is complete; the full meaning
  preservation proof is in progress. See the [implementation record](docs/design/core-runtime-unification-progress.md)
  and [public API guide](docs/design/core-runtime-unification-api.md) for the
  current boundaries and validation results.

## Remaining work

The public source compiler executes the closed specialization slice through Core:
constrained generic calls and first-class function values carry checked trait
evidence, selected unary/binary operator and `Coerce.coerce` bodies include their
helper frontier, and closures share mutable locals, mappings, and proxy values
through one heap. Ground constrained roots resolve their evidence before entry.
The runtime representation recursively erases `comptime<T>` to `T`, while calls
retain marked parameter/result staging checks. Closed staged functions support
closures, mutation, mappings, and arbitrary-precision Integer operations.
Compilation revalidates specialization plans against the checked program and
includes first-class globals discovered inside selected methods.

All public roots use cached Core code and one artifact/value/session API.
Backend preferences and fallback have been removed. Raw-workspace helpers can
select the conventional `main` entry, and ordered compile-many preserves the
requested root order. Existing comptime evaluation remains in the preparation
layer. Its backend unification is a later phase; proving the transformations
actually used by the compiler is part of the meaning preservation work below.

Initial Static Word ABI discovery is also executable. Every function explicitly
exported by the workspace entry module is treated as an intended endpoint and
must resolve to an executable, top-level, ground `Word -> Word` function;
unsupported exported functions are rejected rather than silently omitted.
These roots are source functions, not yet contract public members;
contract-member visibility and ABI integration remain a separate language
boundary.

## Priority implementation

- Generalize evidence passing beyond ground, self-resolved public roots to
  open or caller-supplied dictionaries and unrestricted trait resolution.
- Make staging analysis context-sensitive for locally polymorphic call sites
  whose concrete specializations differ in compile-time availability.
- Add contract-storage field execution when the target source language defines
  that access path. The current upstream source syntax has no general value
  member projection; the latent typed-IR member form is therefore not exposed
  as invented source syntax.
- Add stable serialization for common public values, snapshots, and reusable
  compiler artifacts.
- Integrate ABI discovery with true contract public-member declarations and
  visibility. The current Static Word scan deliberately covers only executable
  top-level functions explicitly exported by the entry module.

## Proof and specification work

- Add declarative raw-source parsing, module/import, and name-resolution
  semantics before the existing resolved-source layer.
- Complete end-to-end correspondence between executable checking, inference,
  staging, specialization, and Core execution and the independent declarative
  `SourceSemantics` judgments; include unification, trait solving, and module
  resolution.
- Connect the remaining general closure, indirect-call, method/coercion, and
  allocation/restoration proofs under one value and heap model. Compose the
  actual compiler passes into result and state preservation and finite Core
  completion reflection through the public compiler API.
- Complete general progress and determinism results, exhaustive fault
  classification, divergence/fuel correspondence, plan-validator completeness,
  and aggregate work bounds. Current finite execution safety does not require
  every checker-accepted program to terminate normally.

## Optional scope extensions

- Extend contract execution beyond one nested-call level and, if desired,
  model richer external-call, creation, storage-layout, gas, and EVM behavior.
- Replace the static Word-only ABI with dynamic and composite ABI support.
- Extend Core generation and shrinking to functions, recursion, algebraic data,
  cells, and host effects, and add an independent cross-implementation
  differential harness.

## Paused

- Parser and diagnostic proof densification, including integration of the
  left-associative trace proof work, remains intentionally deferred.
