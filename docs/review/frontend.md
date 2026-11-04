# Reviewer's guide: Frontend

`Solcore/Frontend` holds two compilers to Core, and an older chain that neither of them uses:

- **The native pipeline.** From a raw workspace to a checked program, a specialization plan, Core
  code and a session. Its entry point is [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean).
- **Rust Hull.** A separate import path for the typed Hull that the pinned Rust compiler exports.
  Its entry point is [`RustHull`](../../Solcore/Frontend/RustHull.lean), and it carries the area's
  main theorems.
- **Fragments.** The historical adapters. The pipeline reaches one module of this chain, the
  numeric literals, and Hull reaches none. Tests still use it, so it stays, and a reviewer can
  skip it.

The [umbrella](../../Solcore/Frontend.lean) gives this reading order in brief.

## Main definitions and theorems

Each entry has its evidence. **README** is "Proof status". **Hull note** is
[Hull meaning preservation](../design/hull-meaning-preservation.md), and **runtime note** is
[Core runtime unification](../design/core-runtime-unification.md). **Root** means that no other
declaration uses it and that it has one of the largest dependency closures of the area. **Path**
means that `SourceCoreExecution.compile` or `Session.run` reaches it.

| Item | Where | Evidence |
| --- | --- | --- |
| The public source API: `SourceCoreExecution.compile`, `Session.run`, `Checkpoint.resume` | [`SourceCompiler`](../../Solcore/Frontend/SourceCompiler.lean), `SourceCoreExecution` | README, runtime note |
| `SourceCoreExecution.compile_checked_source` and its entry and static Word variants | `SourceCoreExecution` | Root |
| `checkProgram` and `checkProgram_success_method_body` | `ProgramChecking` | Root, Path |
| `SourceSpecializationWorklist.run`, `SourceCompilationPlan` | `SourceSpecializationWorklist`, `SourceCompilationPlan` | Path |
| Hull syntax and decoding: `RustHull.Expr`, `RustHull.decodeText` | [`Syntax`](../../Solcore/Frontend/RustHull/Syntax.lean), [`Decode`](../../Solcore/Frontend/RustHull/Decode.lean) | README |
| The independent Hull meaning: `Semantics.EvalFunction` and the effect semantics | [`Semantics`](../../Solcore/Frontend/RustHull/Semantics.lean) and `RustHull/Semantics/` | Hull note |
| The Hull compiler: `lowerExpression`, `assemble`, `Contract.compileObject` | [`Lowering`](../../Solcore/Frontend/RustHull/Lowering.lean), [`Contract`](../../Solcore/Frontend/RustHull/Contract.lean) | Hull note, README |
| Public Hull entry points: `ScalarExecution.prepare`, `LinkedContract.prepareDeployment`, `Contract.runWithReceipt` | [`ScalarExecution`](../../Solcore/Frontend/RustHull/ScalarExecution.lean), [`LinkedContract`](../../Solcore/Frontend/RustHull/LinkedContract.lean), [`Contract`](../../Solcore/Frontend/RustHull/Contract.lean) | README |
| Hull execution safety: `Contract.prepare_resumes_safe`, `ScalarExecution.prepare_resumes_never_faults` | [`Safety`](../../Solcore/Frontend/RustHull/Safety.lean) | README, Hull note |
| Hull function meaning: `Correspondence.prepare_recursive_program_resumes` | [`Correspondence`](../../Solcore/Frontend/RustHull/Correspondence.lean) | Hull note, Root |
| Hull contract meaning: the `prepare_resumes_exact` and `compileObject_resumes_exact` theorems of each effect layer | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean), [`ContractCodeTheorems`](../../Solcore/Frontend/RustHull/ContractCodeTheorems.lean), [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) | Hull note, Root |

## Reading order

1. **Public API.** `SourceCompiler`, then `SourceCoreExecution`.
2. **Checking.** `ProgramInterfaces`, `ProgramImports`, `ProgramTypeResolution`, `ProgramSignatures`,
   `ProgramSignatureFormation`, `TraitResolution`, `SourceInference`, and `ProgramChecking` on top.
3. **Staging and specialization.** `SourceStageAnalysis`, `SourceSpecialization`,
   `SourceSpecializationWorklist` and `SourceCompilationPlan`.
4. **Lowering.** `SourceCoreElaboration`, then `SourceCore/`, then `SourceCoreCompiler` and
   `SourceCoreIndexedSession`.
5. **Rust Hull.** The syntax, the independent meaning, the compiler, and the main theorems.

Everything else is proof machinery in the `Internal/` directories.

## Rust Hull

Read the specification first. It has no reference to Core. Then read the compiler, and then the
theorems that connect the two.

### Specification

| File | Main declarations |
| --- | --- |
| [`Syntax`](../../Solcore/Frontend/RustHull/Syntax.lean) | `Ty`, `Expr`, `Stmt`, `Function`, `YulStmt` |
| [`Decode`](../../Solcore/Frontend/RustHull/Decode.lean) | `decode`, `decodeText`, `DecodeLimits`, `DecodeError` |
| [`Semantics`](../../Solcore/Frontend/RustHull/Semantics.lean) | `Semantics.Value`, `Semantics.State`, `Semantics.Result`, `Semantics.Control`, `Semantics.EvalFunction` |
| [`Semantics/Memory`](../../Solcore/Frontend/RustHull/Semantics/Memory.lean) | `MemorySemantics.State`, `MemorySemantics.builtin`, `MemoryCopySemantics.Operation`, `MemorySnapshotSemantics` |
| [`Semantics/Digests`](../../Solcore/Frontend/RustHull/Semantics/Digests.lean) | `KeccakSemantics.Hash`, `KeccakSemantics.Builtin`, `Sha256Semantics`, `Ripemd160Semantics` |
| [`Semantics/World`](../../Solcore/Frontend/RustHull/Semantics/World.lean) | `StorageSemantics.World`, `EnvironmentSemantics.Operation`, `LogsSemantics`, `CodeImageSemantics`, `AccountObservationSemantics`, `AccountLifecycleSemantics` |
| [`Semantics/Accounts`](../../Solcore/Frontend/RustHull/Semantics/Accounts.lean) | `AccountCallSemantics.Request`, `AccountCallSemantics.Response`, `AccountCallSemantics.Shared`, `AccountCallSemantics.Mode`, `CallTransportSemantics.State` |
| [`Semantics/Layers`](../../Solcore/Frontend/RustHull/Semantics/Layers.lean) | `RuntimeEffectsSemantics.State`, `RuntimeCallEffectsSemantics.State` |
| [`Semantics/Frames`](../../Solcore/Frontend/RustHull/Semantics/Frames.lean) | `RuntimeCallModeSemantics.State`, `RuntimeCallModeSemantics.Operation`, `ChildFrameSemantics.Catalog`, `ChildFrameModeSemantics.Children`, `CreationSemantics`, `YulSemantics` |

### Compiler

The files read in dependency order. Public entry points are at the bottom.

| File | Main declarations |
| --- | --- |
| [`Memory`](../../Solcore/Frontend/RustHull/Memory.lean) | `Memory.packBytes`, `Memory.touch`, `Memory.overflowReason`, `Logs.Event` |
| [`LoweringSupport`](../../Solcore/Frontend/RustHull/LoweringSupport.lean) | `LowerM`, `LoweringError`, `Scope`, `Signature`, `Lowered`, `CodeBuilder.Code` |
| [`Precompiles`](../../Solcore/Frontend/RustHull/Precompiles.lean) | `Keccak.hash`, `Sha256.hash`, `Ripemd160.hash`, `Precompiles.staticCall` |
| [`Effects`](../../Solcore/Frontend/RustHull/Effects.lean) | `AccountState.Account`, `Effects`, `Calls`, `Creation`, `Ambient`, `CreationRuntime`, `AccountInspection`, `AccountLifecycle` |
| [`Lowering`](../../Solcore/Frontend/RustHull/Lowering.lean) | `lowerExpression`, `lowerBuiltin`, `lowerStatement`, `lowerFunction`, `assemble`, `YulLowering.lowerExpr` |
| [`CodeImage`](../../Solcore/Frontend/RustHull/CodeImage.lean) | `CodeImage.Image`, `CodeImage.resolve`, `ObjectLinking.link`, `ImageComparison` |
| [`AccountRuntime`](../../Solcore/Frontend/RustHull/AccountRuntime.lean) | `AccountRuntime.compileFrame`, `AccountRuntime.frameFunction`, `AccountRuntime.References`, `AccountRuntime.CodeDefinition`, `MemorySnapshot` |
| [`Contract`](../../Solcore/Frontend/RustHull/Contract.lean) | `Contract.compileObject`, `Contract.CompiledObject`, `Contract.Context`, `Contract.Receipt`, `Contract.Outcome` |
| [`LinkedContract`](../../Solcore/Frontend/RustHull/LinkedContract.lean) | `LinkedContract.prepare`, `LinkedContract.prepareDeployment`, `LinkedContract.compileObject` |
| [`ScalarExecution`](../../Solcore/Frontend/RustHull/ScalarExecution.lean) | `ScalarExecution.prepare`, `ScalarExecution.run`, `ScalarExecution.resume`, `ScalarExecution.Prepared` |

### Main theorems

The safety theorems assume successful preparation. They exclude Core machine faults, and leave
language failures, reverts and exhausted fuel possible.

A meaning theorem assumes more: successful compilation, syntactic eligibility, an execution that
is not a deployment, and a finite independent source evaluation. The code and call theorems add
premises about catalogs and account links. Each then relates the result, the language fault and the
source state to actual public execution, for every chain of resumptions, and states exactly how
much fuel completes it. The [Hull note](../design/hull-meaning-preservation.md) says what each one
covers.

| Result | Theorems | File |
| --- | --- | --- |
| No machine fault, scalar | `ScalarExecution.prepare_resumes_never_faults`, `ScalarExecution.prepare_resumes_hasType` | [`Safety`](../../Solcore/Frontend/RustHull/Safety.lean) |
| No machine fault, contracts | `Contract.prepare_resumes_safe`, `LinkedContract.prepare_resumes_safe` | [`Safety`](../../Solcore/Frontend/RustHull/Safety.lean) |
| Recursive programs | `Correspondence.prepare_recursive_program_resumes` | [`Correspondence`](../../Solcore/Frontend/RustHull/Correspondence.lean) |
| Ranked and pure programs | `Correspondence.prepare_ranked_program_resumes`, `Correspondence.prepare_pure_program_resumes` | [`Correspondence`](../../Solcore/Frontend/RustHull/Correspondence.lean) |
| Memory | `ContractMemoryCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Storage and transient storage | `ContractRuntimeEffectsCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Message and block observations | `ContractEnvironmentCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Logs | `ContractLogCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Explicit termination | `ContractFullCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Memory and calldata copies | `ContractCopyCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Keccak | `ContractHashCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Account observation | `ContractAccountCorrespondence.prepare_resumes_exact` | [`ContractStateTheorems`](../../Solcore/Frontend/RustHull/ContractStateTheorems.lean) |
| Code images and catalogs | `ContractCodeCorrespondence.compileObject_resumes_exact` | [`ContractCodeTheorems`](../../Solcore/Frontend/RustHull/ContractCodeTheorems.lean) |
| Return data | `ContractReturnDataCorrespondence.compileObject_resumes_exact`, `ContractReturnDataCorrespondence.prepare_resumes_exact` | [`ContractCodeTheorems`](../../Solcore/Frontend/RustHull/ContractCodeTheorems.lean) |
| CALL and STATICCALL | `ContractCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| Compiled children | `ContractChildCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| Finite call trees | `ContractNestedChildCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| All four call modes, and account destruction | `ContractCallModeCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |
| Root reentry | `ContractRootCallCorrespondence.compileObject_resumes_exact` | [`ContractCallTheorems`](../../Solcore/Frontend/RustHull/ContractCallTheorems.lean) |

The same layers have frame-level results below these, each named `compileFrame_preserves`, in
`Internal/EffectLayers`, `Internal/TerminationLayers`, `Internal/AccountLayers`,
`Internal/CallEffects` and `Internal/LinkedWorld`.

### Internal

| File | Topic |
| --- | --- |
| [`Internal/AccountCalls`](../../Solcore/Frontend/RustHull/Internal/AccountCalls.lean) | Actual account dispatch against its independent rule: checkpoints, transfers, child selection, call modes and account destruction. |
| [`Internal/AccountLayers`](../../Solcore/Frontend/RustHull/Internal/AccountLayers.lean) | The frame and message proofs of the account, code and return data layers. |
| [`Internal/CallBuiltins`](../../Solcore/Frontend/RustHull/Internal/CallBuiltins.lean) | CALL, STATICCALL, CALLCODE, DELEGATECALL, SELFDESTRUCT, revert and inline Yul through the actual builtin compiler. |
| [`Internal/CallEffects`](../../Solcore/Frontend/RustHull/Internal/CallEffects.lean) | The frame and message proofs of the call, child call and call mode layers. |
| [`Internal/CallLayout`](../../Solcore/Frontend/RustHull/Internal/CallLayout.lean) | The layout and state relation of the call layer, and the effects a call supports. It stays apart from `Internal/CallStates`: `call_fixed_separation` unfolds `Layout` millions of times, and that costs a quarter more heartbeats, past the limit, when `Layout` is declared in the same file. |
| [`Internal/CallStates`](../../Solcore/Frontend/RustHull/Internal/CallStates.lean) | The resources and updates of the call layers, and their installed callbacks. |
| [`Internal/CallTransport`](../../Solcore/Frontend/RustHull/Internal/CallTransport.lean) | Caller-frame transport and the identity precompile, with the call builtin compiler facts. |
| [`Internal/ChildFrameCalls`](../../Solcore/Frontend/RustHull/Internal/ChildFrameCalls.lean) | Finite call trees: nested children, call modes and root reentry, with their catalog links. |
| [`Internal/ChildFrames`](../../Solcore/Frontend/RustHull/Internal/ChildFrames.lean) | Fresh child frames: allocation, shared resources, invocation and completion. |
| [`Internal/Creation`](../../Solcore/Frontend/RustHull/Internal/Creation.lean) | Address derivation, preimages, handlers and transport of CREATE and CREATE2. |
| [`Internal/CreationBuiltin`](../../Solcore/Frontend/RustHull/Internal/CreationBuiltin.lean) | Actual CREATE and CREATE2 lowering against `CreationSemantics`. |
| [`Internal/Derivations`](../../Solcore/Frontend/RustHull/Internal/Derivations.lean) | Simulation by induction on a finite independent Hull derivation: atoms, expressions, calls, statements, loops, matches, faults and inline Yul. |
| [`Internal/Digests`](../../Solcore/Frontend/RustHull/Internal/Digests.lean) | The Core Keccak, SHA-256 and RIPEMD-160 against their independent definitions, block by block. |
| [`Internal/EffectBuiltins`](../../Solcore/Frontend/RustHull/Internal/EffectBuiltins.lean) | Memory, storage, log, Keccak, environment and account observation builtins through the actual builtin compiler. |
| [`Internal/EffectLayers`](../../Solcore/Frontend/RustHull/Internal/EffectLayers.lean) | The frame and message proofs of the storage, environment and log layers. |
| [`Internal/LinkedWorld`](../../Solcore/Frontend/RustHull/Internal/LinkedWorld.lean) | Exact catalog links and executable identities survive every call-free operation. |
| [`Internal/LoweringFacts`](../../Solcore/Frontend/RustHull/Internal/LoweringFacts.lean) | Shapes of the lowering output, literal parsing, scope coverage, and the exact execution of a scalar or contract receipt. |
| [`Internal/MemoryState`](../../Solcore/Frontend/RustHull/Internal/MemoryState.lean) | Core memory, range copies and logs against the independent state. |
| [`Internal/NamedFunctions`](../../Solcore/Frontend/RustHull/Internal/NamedFunctions.lean) | Function installation, parameter initialization and calls to named functions within one compiled program. |
| [`Internal/PublicFunctions`](../../Solcore/Frontend/RustHull/Internal/PublicFunctions.lean) | The public theorems for call-free and single functions, and the ranked expression interface that the program theorems use. |
| [`Internal/RuntimeFrames`](../../Solcore/Frontend/RustHull/Internal/RuntimeFrames.lean) | One compiled frame: its closures, memory initialization, completion and frame facts. |
| [`Internal/RuntimeObjects`](../../Solcore/Frontend/RustHull/Internal/RuntimeObjects.lean) | Object initialization, allocation locations, installed callbacks and the code catalog, and the first memory contract layer. |
| [`Internal/Statements`](../../Solcore/Frontend/RustHull/Internal/Statements.lean) | Operational correspondence for expressions, patterns, assignments and straight-line statements in the actual lowering output. |
| [`Internal/StorageState`](../../Solcore/Frontend/RustHull/Internal/StorageState.lean) | Core storage against the independent world, and the state relation of the effect runtime. |
| [`Internal/TerminationLayers`](../../Solcore/Frontend/RustHull/Internal/TerminationLayers.lean) | The frame and message proofs of the termination, copy and hash layers. |

## What a reviewer should know

- **Hull is one directory with one entry.** Nothing in the native pipeline imports it. Only the
  generators reach into it, for `Keccak` and `Memory`, and `RustHull/Memory` keeps those free of
  Hull syntax.
- **Public theorems sit above frame results.** A `compileFrame_preserves` theorem is a step toward
  a contract theorem. The contract theorem is the claim, because it starts at actual compilation
  and ends at public receipts.
- **Three separations are deliberate.**
  - `Logs` shares `RustHull/Memory`, below `Syntax`. It means `Core.Expr` through an `open`, and
    `RustHull.Expr` would shadow that once `Syntax` is in reach.
  - `CreationRuntime` stays in `RustHull/Effects`, below `Lowering`. It takes `boolean` from
    `CodeBuilder`, and `Lowering` declares a `boolean` of its own.
  - `Internal/CallLayout` stays apart from `Internal/CallStates`. `call_fixed_separation` unfolds
    `Layout` about 2.6 million times. Lean looks up a constant of the current file more slowly than
    an imported one, so with `Layout` in the same file the proof costs 223,663 heartbeats instead
    of 176,580, past the limit of 200,000.
