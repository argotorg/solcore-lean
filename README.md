# solcore-lean

Implemented behavior is defined by the Lean modules and checked by the
repository tests. This README keeps only a compact module guide and the
unfinished work.

## Module guide

External users should normally import an umbrella module instead of a leaf
implementation or proof module. The typical executable flow is
`Workspace / Syntax` → `Frontend.Current` (using `TypeSystem` and `Resolved`)
→ `Core` or the typed-source runtime → `ContractRuntime`. `SourceSemantics`
is the independent, proof-facing specification of resolved source programs.

| Module | Responsibility |
| --- | --- |
| [`Solcore`](Solcore.lean) | Main umbrella for the source frontend, declarative source semantics, Core, contract runtime, ABI, synthesis, workspace, and utilities. Optional boundaries such as Core Wire remain explicit imports. |
| [`Solcore.Spec`](Solcore/Spec.lean) | Pure umbrella for `Syntax`, `Core`, and `ContractRuntime`. It is not the complete frontend or complete source-semantics umbrella. |
| [`Solcore.Util`](Solcore/Util.lean) | Shared fixed-radix, fixed-width hexadecimal, and JSON helpers; it contains no language semantics. |
| [`Solcore.Workspace`](Solcore/Workspace.lean) | Canonical source/library identities and structural workspace validation. Module and name resolution happen later. |
| [`Solcore.Syntax`](Solcore/Syntax.lean) | Source-preserving AST, lexer, parser, diagnostics, declarative grammars, and parser correctness properties. |
| [`Solcore.Resolved`](Solcore/Resolved.lean) | Small already-resolved local-expression semantics with scope, typing, evaluation, renaming, lowering, and Core correspondence. It is not the whole-program name resolver. |
| [`Solcore.TypeSystem`](Solcore/TypeSystem.lean) | Source types, substitutions, first-order unification, rank-1 schemes, inference state, and their basic properties. |
| [`Solcore.Frontend.Current`](Solcore/Frontend/Current.lean) | Preferred executable whole-program entry: loading, resolution, inference, staging, specialization, linking, backend selection, and execution. |
| [`Solcore.Frontend`](Solcore/Frontend.lean) | Compatibility facade containing `Frontend.Current` and the older focused adapters under `Frontend.Fragments`. |
| [`Solcore.SourceSemantics`](Solcore/SourceSemantics.lean) | Algorithm-independent static, staging, dynamic, fault, substitution, and preservation judgments for resolved typed source. |
| [`Solcore.Core`](Solcore/Core.lean) | Typed Semantic Core syntax, stores, evaluator and machines, primitives, checker, runners, safety, and correspondence theorems. |
| [`Solcore.Core.Wire`](Solcore/Core/Wire.lean) | Canonical external Core representation, Core conversion, fixed host boundary, strict JSON codecs, and decode budgets. |
| [`Solcore.ContractRuntime`](Solcore/ContractRuntime.lean) | Checked-Core execution over accounts and world state: host effects, storage, frames, transactions, calls, creation, commit/rollback, and observations. |
| [`Solcore.Abi`](Solcore/Abi.lean) | Keccak-256 and the currently supported static-Word ABI codec and dispatch layer. |
| [`Solcore.Synthesis`](Solcore/Synthesis.lean) | Reproducible generation and shrinking of checker-accepted Semantic Core programs. |
| [`Solcore.Semantics`](Solcore/Semantics.lean) | Deprecated compatibility import for `Solcore.ContractRuntime`; new code should not use it. |

Umbrella files are the navigation and import boundaries for downstream code.
Leaf files, `*Properties` modules, parser grammar/trace units, and
`Frontend.Fragments` are focused implementation or proof units.

## Contributor map

- Definitions and proofs live below `Solcore/`; place a proof close to the
  definition it establishes, usually in the adjacent `*Properties` module.
- Test modules and reusable fixtures live below `Solcore/Test/`.
  [`Tests/Main.lean`](Tests/Main.lean) imports the suites and registers their
  executable checks.
- Run `lake build`, `lake test`, and `node scripts/check-kernel.mjs` before
  submitting a change. Warnings are errors, and the kernel-policy check rejects
  proof escape hatches in semantic modules.

## Remaining work

## Priority implementation

- Broaden whole-program execution to cover advanced generic/type cases,
  coherent unrestricted trait resolution, more deeply nested and constrained
  let-polymorphic runtime values, general evidence/coercion dispatch, members,
  mappings, proxies, mutation, and higher-order or effectful staging.
- Complete public compiler orchestration: automatic entry and ABI-root
  discovery, multi-root and mixed-backend compilation, backend override, and
  serialization of source values, closures, heaps, and results.

## Proof and specification work

- Add declarative raw-source parsing, module/import, and name-resolution
  semantics before the existing resolved-source layer.
- Prove end-to-end soundness, completeness, and correspondence from checking,
  inference, staging, and specialization through every execution backend;
  include unification, trait solving, and module resolution.
- Complete general progress and determinism results, exhaustive fault
  classification, divergence/fuel correspondence, backend-uniform deep
  preservation, plan-validator completeness, and aggregate work bounds.

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
