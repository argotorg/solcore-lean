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
| [`Solcore.Frontend.Current`](Solcore/Frontend/Current.lean) | Preferred executable whole-program entry: loading, resolution, inference, staging, specialization, linking, reusable compilation, root discovery, backend selection, execution, and backend-native/deep result certificates. |
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

The two preservation boundaries are intentionally distinct.
[`WholeLanguagePreservation`](Solcore/SourceSemantics/Dynamic/WholeLanguagePreservation.lean)
is the constructive, algorithm-independent mutual preservation proof for
declarative resolved-source evaluation, and
[`ProgramEvaluates.preserves`](Solcore/SourceSemantics/Dynamic/Program.lean)
lifts it to the whole-program entry judgment.
[`SourceTypedRuntimeDeepSafety`](Solcore/Frontend/SourceTypedRuntimeDeepSafety.lean)
is the executable typed-source boundary certificate: a normal public run
certifies deeply typed initial/final heaps, inputs/results, readable captures,
heap type-layout extension, checked-plan substitution-image code provenance,
and authenticated evidence. [`SourceCompiler`](Solcore/Frontend/SourceCompiler.lean)
exposes both the complete pre/post certificate and its final-result projection.
Correspondence between this executable pipeline and the independent
declarative judgments remains future work.

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

The typed-source backend now executes the closed specialization slice end to
end: constrained generic calls and first-class function values carry checked
trait evidence, selected unary/binary operator and `Coerce.coerce` bodies run
with their complete helper frontier, and closures share mutable locals,
mappings, and proxy values through one runtime heap. Ground constrained roots
resolve their own evidence before entry. `comptime<T>` is recursively erased
to `T` at the runtime representation boundary, while direct and first-class
calls still enforce marked parameter/result staging. Closed staged functions
can combine closures, mutation, and mappings, and arbitrary-precision Integer
values execute arithmetic, comparisons, complement, and bitwise operations.
Public result typing uses the complete prepared plan, including first-class
globals discovered only inside a selected operator or coercion method.
The safe typed-source entry also replays caller-supplied specialization plans
against the checked program before execution, rejecting altered generic
operator requirements even when the specialized operands are builtin types.

The public source compiler now owns the initial orchestration policy. Automatic
selection tries direct Semantic Core first and the typed-source runtime second;
the obsolete finite call-graph backend and its legacy fallback have been
removed. A backend preference can force either remaining backend, and automatic
exhaustion and explicit-backend rejection use one backend-tagged diagnostic
carrier. Raw-workspace helpers can select the conventional `main` entry
automatically, while ordered compile-many preserves the requested root order
and permits different roots to select different backends.

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
- Add stable serialization for source values, closures, heaps, backend-tagged
  results, and the reusable compiler boundary.
- Integrate ABI discovery with true contract public-member declarations and
  visibility. The current Static Word scan deliberately covers only executable
  top-level functions explicitly exported by the entry module.

## Proof and specification work

- Add declarative raw-source parsing, module/import, and name-resolution
  semantics before the existing resolved-source layer.
- Prove end-to-end correspondence between executable checking, inference,
  staging, specialization, and each runtime, and the independent declarative
  `SourceSemantics` judgments; include unification, trait solving, and module
  resolution.
- Replace the typed-source runtime's checked pre/post execution certificate
  with, or supplement it by, an inductive preservation proof for the evaluator
  itself. The removed call-graph backend had this narrower guarantee for its
  recursion/closure fragment; typed-source covers more language features but
  currently validates deep safety at the executable boundary.
- Complete general progress and determinism results, exhaustive fault
  classification, divergence/fuel correspondence, plan-validator completeness,
  aggregate work bounds, and—if useful—a single backend-independent
  formulation combining the existing backend-native preservation results.

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
