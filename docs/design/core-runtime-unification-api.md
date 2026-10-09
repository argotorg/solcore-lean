# Migration to the common Core execution API

Last updated: 2026-10-09.

Runtime unification and removal of the old typed-source evaluator were completed in `a3168382`. This document describes the current public API. The second goal, the proof of meaning preservation for the complete public compiler, remains in progress. See the [implementation record](core-runtime-unification-progress.md) for the latest implementation and validation checkpoint.

## Public entry points

`Solcore.Frontend.SourceCompiler` reexports the types and functions of `SourceCoreExecution`. It has no separate backend, compiler representation, or session implementation.

| Role of the old API | Current entry point |
| --- | --- |
| Backend preference and fallback | Removed. All entries prepare the same Core artifact. |
| A single `main` | `compileEntry raw options` / `compileEntryChecked program moduleId options` |
| Multiple roots specified by name and type arguments | `compile raw seeds options` / `compileChecked program seeds options` |
| StaticWord selector discovery | `compileStaticWord raw options` / `compileStaticWordChecked program moduleId options` |
| Creating execution state | `compiled.open` → `artifact.bootstrap` → `Bootstrap.resume fuel` |
| Running a root | `session.run key arguments runOptions` |
| Calling a returned function again | `session.invokePacked handle packedArgument runOptions` |
| Named functions and builtins as arguments | Use Completion.value from `session.named key` / `session.builtin builtinId`. |
| Continuing after fuel exhaustion | `Outcome.outOfFuel checkpoint` → `checkpoint.resume fuel outputValidationFuel` |
| Observing the heap and restoring execution | `session.snapshot` / `checkpoint.snapshot` → `snapshot.restore` |
| Reusing the original initial heap | `snapshot.prefix` → `artifact.bootstrapFromPrefix` |
| Using the entire source heap as a new session's initial heap | `snapshot.exportPrefix` → `artifact.bootstrapFromPrefix` |
| Ordinary initial heap | A list of `SourceCoreHeapInput.Cell` containing common Value data → `artifact.preparePrefix` |
| Importing historical raw state | Explicitly import `SourceCoreLegacyHeapImport` and use its `preparePrefix`. |

`Frontend/SourceCompilerSession.lean` has been removed. The test module `Test/SourceCompilerSession.lean` tests the common API; it does not provide another implementation of the old session.

## Values and ownership

Execution uses one Value representation for Unit, Bool, Word, Integer, products, nominal constructors, ordered mappings, proxies, and function handles. Public Value exposes no source closure, source body, or native cell reference.

A Handle belongs to an artifact, session, export generation, and slot. An existing session's issuer is private, so callers cannot manufacture arbitrary handles with the same ownership. Mixing artifacts or sessions, supplying an unknown handle, or supplying a value of the wrong type produces a boundary error before execution.

Packed arguments use `.unit` for 0 arguments, the value itself for 1 argument, and the existing right-associated product layout for multiple arguments. Direct handle calls preserve the callee's staged parameter/result constraints.

## Outcomes and budgets

`RunOptions` separates `inputValidationFuel`, `executionFuel`, and `outputValidationFuel`. These are independent of the checking, specialization, and compilation budgets in `Options`. Core execution uses a different number of steps from the old direct evaluator.

`Session.run` / `invokePacked` returns `IO (Except SourceCoreIndexedSession.Error (Outcome artifact))`. `Checkpoint.resume` returns `IO (Outcome artifact)`.

- Outer error: rejection at the argument, ownership, or call boundary.
- `succeeded`: a common Value and the updated session. `Completion.typed` guarantees value authentication within the same ownership domain.
- `failed`: a source-language failure and the session at that point. Obtain a source diagnostic with `session.diagnostic key reason` or `handleDiagnostic`.
- `outOfFuel`: a typed checkpoint. Resumption continues from the saved Core continuation.
- `exportError`: a failure of output boundary validation, an insufficient observation budget, or a similar export error, together with the session.

## Snapshots and prefixes

A Snapshot retains the typed native store, world, registry, and, when needed, execution continuation from the time it was taken. `restore` also preserves the ready/suspended classification. `session.restoreSnapshot snapshot` requires ownership by the same session.

`Snapshot.cells` follows source-location order and excludes Core administrative cells. `Snapshot.heapSize` and `PrefixSnapshot.heapSize` count source cells; `Snapshot.nativeHeapSize` counts native-store cells. `Session.heapSize` and `Checkpoint.heapSize` also count native-store cells. Observe an allocation in progress through `pendingAllocation`.

A monomorphic callable is observed as a handle that can be authenticated by the registry at the snapshot's restoration destination. The same callable reuses its existing handle when already registered. Newly observed handles are not implicitly added to the registry from which the snapshot was taken.

A generic principal is a readonly observation of its scheme, type, captures, and evidence; it is not a closed callable handle. Source bodies and native references remain private. The original prefix is an inert, readonly observation.

`snapshot.prefix` is the **prefix originally supplied as input**. `exportPrefix` restores that prefix and every recorded source cell, passes them through the deep validator, and produces a separate sealed prefix. A new session keeps that prefix inert, and source locations for new allocations start at its length. Original handles and native continuations do not transfer to the new session. Prefix migration to a different artifact is not provided.

## Initial input

`artifact.preparePrefix cells validationFuel conversionFuel` converts common Value data and uninitialized cells, then applies the existing deep heap validation. It preserves nominal metadata, duplicate mapping keys, and entry order. Payloads that do not match their types are rejected.

A callable handle alone cannot be placed in an initial cell. Use `snapshot.exportPrefix`, which carries evidence of actual captures and allocations. A historical raw initial heap containing closures is validated by the explicit migration module with its existing acceptance conditions and budgets. This process does not execute source expressions or statements.

An artifact with an empty root set accepts only an empty heap and rejects all calls. A nonempty initial heap supplied to an empty root set is rejected rather than silently discarded.

## Implementation examples

- Compilation, roots, sessions, and ownership: [SourceCoreExecution](../../Solcore/Test/SourceCoreExecution.lean)
- Public snapshots, initial data, full prefixes, principals, failures, and continuations: [SourceCoreExecutionSnapshots](../../Solcore/Test/SourceCoreExecutionSnapshots.lean)
- Export of deep raw metadata, generic/read views, and caller/lexical profiles: [SourceCoreActiveHeapPrefix](../../Solcore/Test/SourceCoreActiveHeapPrefix.lean)
- Auditing public execution and internal evidence for the same artifact: [SourceCompilerFeatureSupport](../../Solcore/Test/SourceCompilerFeatureSupport.lean)
- Definitional identity of the public facade and common API: [SourceCoreUnifiedImportBoundary](../../Solcore/Test/SourceCoreUnifiedImportBoundary.lean)

## Selected literal proof interfaces

These internal proof modules connect the actual accepted compiler to a selected Word literal, singleton return body and invocation. They do not yet establish the final theorem for the complete public compiler.

| Module | Available connection |
| --- | --- |
| `CallableIndexedOwnedSingletonReturnCompilerReceipts` | `Receipt`, `of_return`, `functions_child` and `at_root` retain the original accepted child, emitted finish and actual compiler callback budget. |
| `CallableIndexedOwnedChosenWordLiteralExpressionBounds` | `WordNodeFacts` and `certificate_at_support` connect actual numeric evidence to the same selected Support. `preserves_at_support` and `reflects_at_support` prove admitted literal execution semantics. |
| `CallableIndexedOwnedLiteralLambdaBodyContinuations` | `support_flow_preserves` and `support_flow_reflects` derive the return child from actual coverage. `source_at_entry` / `native_at_entry` and `source_continuation` / `native_continuation` use genuine parameter admission and the original finish. |
| `SourceCoreChosenOrdinaryAcceptedLiteralSupport` | The accepted fixture derives its current-context domain, local absence of indirect calls, recaptured factories and expression tree internally. |
| `SourceCoreChosenOrdinaryAcceptedLiteralCompilerReceipts` | The same fixture derives Word facts and original compiler receipts, then exposes preservation and reflection at its selected Support. |
| `CallableIndexedOwnedChosenOrdinaryInitializedReadAdmission` | `source_value_typed`, `post_admission` and `callee_post` derive admission and the callee value relation from the actual initialized Source cell and occurrence typing. |
| `CallableIndexedOwnedLiteralLambdaInvocationBounds` | Invocation and application preservation/reflection derive body continuations internally and retain actual marked parameters, the reached pool and saved caller restoration. |
| `SourceCoreChosenOrdinaryAcceptedArgumentAdmission` | Actual numeric Source evaluations construct the physical pair, exclude argument faults and derive raw argument typing and admission at the same reached heap. |
| `SourceCoreChosenOrdinaryAcceptedLiteralInvocation` | The accepted fixture derives its body context, Word facts and compiler receipts internally, then instantiates invocation and application bounds. |
| `SourceCoreChosenOrdinaryAcceptedLiteralCallGuard` | Derives runtime parameter shape, Source stage acceptance, physical arity and the selected dispatch row's complete acceptance from genuine compiler and contract receipts. |
| `SourceCoreChosenOrdinaryAcceptedParentCompilerReceipts` | Retains original parent acceptance, callee and argument compiler receipts, Prepared callsite and chosen root under the same policy, Header and body lowerer. |
| `SourceCoreChosenOrdinaryAcceptedPairArgumentBounds` | Derives the pair argument tree from parent acceptance and closes preservation/reflection using actual literal and tuple producers, with admission and all rows. |
| `SourceCoreChosenOrdinaryAcceptedLiteralStoredApplication` | Derives final Source heap admission from actual call allocation and return; reflects the original fourth bind into a real parent Source outcome, retaining genuine dispatch, captures and complete prefix witnesses. |

The literal invocation derives its body ledger and runtime validity from the same selected Support. Genuine capture/global correspondence, argument typing, deep Source heap typing and the complete ordered record relation remain explicit where needed. Source and native grades are independent. The approved child is literal occurrence 3; the outer indirect parent at occurrence 5 remains in the Source. The actual pair compiler tree and selected-row acceptance are connected. Deriving the actual sidecar/dispatch association and complete native prefix from whole parent completion, then closing the shared mixed body family, is ongoing.

The old `SourceTypedRuntime` namespace remains in compatibility value, observation, and validation carriers. Its name does not imply that a runtime evaluator of Source expressions and statements remains.

Moving the comptime evaluator to Core and adding source contract/storage/external-call connections are the agreed next phase. Meaning preservation for comptime transformations actually performed by the current compiler is part of the second goal.
