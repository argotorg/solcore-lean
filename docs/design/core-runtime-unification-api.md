# Migration to the common Core execution API

Last updated: 2026-10-11.

Runtime unification and removal of the old typed-source evaluator were completed in `a3168382`. This document describes the current public API. The second goal, the proof of meaning preservation for the complete public compiler, remains in progress. See the [implementation record](core-runtime-unification-progress.md) for the latest implementation and validation checkpoint.

## Latest verified proof interfaces (2026-10-11)

The public runtime entry points below remain unchanged. The latest recursive caller/body additions are committed in `a6cb5ab2` and `2f22789d`: six Sources expose 12 checked interfaces with literal private/normal agreement for 70 owned declarations.

- `SelectedBodyCompilerRoots` issues original Source certificates from authentic accepted compiler actions. `SelectedBodySupportFactories` and `SelectedCompilerTerminalCallerBounds` construct exact static support and consume the supported recursive caller proof; their original unit was verified in `d5d5e123` and `02006e66`. The constructive replacement `db1ab3d2` preserves its 25 public interface types.
- `SelectedBodyCompilerCallbacks`, `SelectedNamedCompilerRecipes` and the selected closure/named factories retain the same contextual compiler site, actual body, callback, chosen packet and raw parameter authority. They derive support for those genuine occurrences; an arbitrary earlier Association or unrelated compiler site is not upgraded.
- `DiscardSourceBodyInversion`, the discard compiler receipts and the flow/body bounds retain the original discard/return forms, actual child compiler actions, raw typing, intermediate state and literal emitted footer. Source and native grades remain independent.
- `MixedBodyStaticSupport` and `MixedBodyCompilerSupport` retain terminal/discard packets and original roots at the same Code and parameter context. The mixed flow, body, lambda application, contextual application and parent bounds preserve the actual caller restoration for ordinary and principal Associations.
- The mixed user/indirect dispatch and call-head bounds feed `MixedRecursiveCallerBounds` and `MixedRecursiveBodyBounds`. The final body endpoints construct both execution directions internally, retaining the original Root contracts and exact caller post. They require static support for actual Associations and terminal named bodies.

These ports keep genuine compiler policy/read conditions, original typing and call readiness explicit. Complete formation factories, wider Source grammar and the final public all-pass theorem remain incomplete. The seven static witness replacements at `87b08905` expose 47 checked interfaces. Seed and Inventory indices are intentional proof-interface changes; profile constructors return proposition-valued existence. Complete private/normal TYPE/AXIOMS and API logs agree, and registered tests and the repository policy checker pass with zero findings. The full public semantics theorem remains incomplete.

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

These internal proof modules connect the actual accepted compiler to a selected Word literal, singleton return body, invocation and successful public program result for the retained fixture. The final theorem for the complete public compiler remains unfinished.

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
| `CallableIndexedOwnedChosenOrdinaryArgumentBundles` | `native_type`, `compiler_parameters`, `compiler_parameter_pack` and `arguments_at_compiler` derive native signature and argument alignment from the known chosen carrier and actual callee value relation. |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchReceipts` | `Receipt` and `at_chosen_parent` retain the original sidecar, lambda origin, codebook rows, dispatch and selection at the same actual Prepared callsite. |
| `CallableIndexedOwnedStoredIndirectPurePrefixBounds` | `reflects_arguments` and `reflects_parent` extract the actual ordered argument post and full successful runtime prefix from Core completion, keeping the measured application child. |
| `SourceCoreChosenOrdinaryAcceptedParentEntryReceipts` | `fixture_compilation` / `fixture_root` transport only the genuine Header named index. `pair_at_chosen_parent`, `parent_declarations` and `callee_at_parent` derive the closed pair and initialized read producers from the original accepted parent. |
| `CallableIndexedOwnedChosenOrdinaryCallDispatchSourceTransport` | Transports the actual sidecar, lambda origin, dispatch and selected rows along genuine Source equality while retaining the same chosen compiler root. |
| `SourceCoreChosenOrdinaryAcceptedParentArgumentOutcomes` | `values_at`, `noFault` and `evaluates` retain the actual singleton pair arguments and unchanged heap from independent Source traces. |
| `SourceCoreChosenOrdinaryAcceptedParentPreservationBounds` | `preserves_parent_at_initialized` derives whole Core parent evaluation and the full admitted result from the actual Source parent outcome. |
| `SourceCoreChosenOrdinaryAcceptedParentReflectionBounds` | `reflects_parent_at_initialized` derives the independent Source parent outcome and full admitted result from whole Core completion. |
| `SourceCoreChosenOrdinaryAcceptedOuterCompilerReceipts` | `of_body`, `emitted_at_header` and `at_original_root` retain actual initializer, Allocation/Annotated and flow/finish compiler receipts at the same root. |
| `SourceCoreChosenOrdinaryAcceptedInitializerAdmission` | `receipt_value_has_type`, `receipt_outcome_at` and `receipt_post_admission` derive the same selected closure's raw typing, pure Source outcome and unchanged-state admission from genuine coverage and captures. |
| `CallableIndexedOwnedChosenOrdinaryInitializedAllocationState` | `allocate_initialized` runs the original stateful allocator once and returns its full reached tuple, admission and positive chosen stored member. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyBounds` | `whole_from_parent_value` / `whole_from_parent_fault` compose actual native children. `parent_at_whole_completion` extracts the genuine strict child; `source_parent_at_body` inverts the independent Source body. |
| `SourceCoreChosenOrdinaryAcceptedHeaderEvidence` | `header_exists_with_evidence` and `header_fixture_with_evidence` retain `HeaderAt` and empty evidence from the same authentic Header constructor. |
| `SourceCoreChosenOrdinaryAcceptedInitializedEntry` | `initialized_entry` runs one original formation and one stateful initialized allocation, retaining the actual reached tuple, original history and positive stored member. |
| `SourceCoreChosenOrdinaryAcceptedOuterSourceConstruction` | `body_from_parent_value` / `body_from_parent_fault` and `body_trace_at_header` construct the original two-statement Source body. `post_admission_at_runtime` transports raw typing to Γ0 at the same reached state and rows. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyPreservationBounds` | `preserves_body` and `reflects_body` derive complete accepted-body correspondence and `BodyResultAt`, including cumulative effects, the actual restored caller and successful raw admission. |
| `SourceCoreChosenOrdinaryAcceptedBodyStatePorts` | Derives empty Source entry, actual captures, global references, native store typing, readiness and admission from the same real named parameter Receipt. |
| `SourceCoreChosenOrdinaryAcceptedInitialBodyAdmission` | Derives deep typing after the genuine empty-parameter allocation and every stable row after the actual singleton hook installation and parameter effects. |
| `SourceCoreChosenOrdinaryAcceptedHeaderRuntimeEvidence` | Retains global count and empty evidence from the same authentic Header constructor. |
| `SourceCoreChosenOrdinaryAcceptedBodyStateCorrespondence` | `preserves_at_receipt` / `reflects_at_receipt` derive admitted whole-body correspondence at the actual reached pool. `source_body_at` / `native_body_at` implement the existing body interfaces. |
| `RecursiveNamedCatalogPreparedInitializationReceipts` | `stored_capture` and `entry_with_constructor` construct the actual initialization authority and retain its prescribed live capture, exact initialized store and empty Source heap relation. |
| `SourceCoreChosenOrdinaryAcceptedPublicBootstrapReceipt` | `PublicRecipeReceipt`, `CompletedBootstrap` and `completed_store` retain one original preparation and one machine completion. `accepted_public_fixture` provides the positive executable receipt. |
| `SourceCoreChosenOrdinaryAcceptedBootstrapHeaderEvidence` | `BootstrapEvidence`, `header_exists_with_bootstrap` and `header_fixture_with_bootstrap` retain the same authentic Header, runtime evidence, layouts and empty Source captures. |
| `SourceCoreChosenOrdinaryAcceptedPublicParameterEntry` | `catalog_complete`, `catalog_ledger`, `initial_at_completed` and `parameter_entry` derive the actual initial state and named parameter Receipt. `ParameterAgreement` retains its original prefix/body ContinuationAgreement. |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyCorrespondence` | `at_completed` constructs the same actual parameter Receipt and `BodyAtReceipt`, including admitted body preservation/reflection and SourceBodyAt/NativeBodyAt. |
| `SourceCoreChosenOrdinaryAcceptedPublicInvocation` | `source_continuation_at_initial` / `native_continuation_at_initial`, `preserves_at_initial` / `reflects_at_initial` and `at_completed` derive original named invocation at the actual initial store. The low result keeps restoration and cumulative effects. |
| `SourceCoreIndexedSession` | `RecipeAt`, `InitialAt`, `NativeDone`, `NativeAt` and `BootstrappedFrom` retain original construction. `resumeWithReceipt` and `ResumeAt` share the actual resume action; `succeeded` / `failed` retain its real completion. `SucceededResultAt.source_type` / `word_value` and `ResumeAt.word_succeeded` use authentic request/export acceptance. Legacy operational signatures remain unchanged. |
| `SourceCoreChosenOrdinaryAcceptedPublicSessionEntry` | `accepted_public_session_fixture` retains the original public IO chain. `completed_at_ready`, `body_at_session` and `invocation_at_session` connect its actual ready Session to the same initialized store, world and static registry. Normal full/API checks and the positive ready runner pass. |
| `SourceCoreChosenOrdinaryAcceptedOriginalProgramAdmission` | `originalCatalog`, `program_well_formed` and `program_has_stages` derive genuine original Source admission from full finite catalog equality, original checker typing and actual stage analysis. |
| `SourceCoreChosenOrdinaryAcceptedPublicRootStart` | `at_session`, `preserves_root` and `reflects_root` connect actual successful Session.start and the original invocation to the same checkpoint and initialization store. |
| `SourceCoreChosenOrdinaryAcceptedPublicResultObservation` | `observe`, `Observation.word_iff` and `Observation.fault_iff` retain identical Words or the genuine fault relation from the complete low invocation result. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramOutcome` | `at_started`, `native_completed_reflects_program`, `program_has_sufficient_native_fuel`, `public_succeeded_reflects_program` and `program_word_preserved` connect independent admitted ProgramOutcome to actual native completion and successful Word export. `accepted_public_program_run` retains one original public action chain. |
| `CallableIndexedOwnedNamedProgramAdmission` | `after_program_outcome` derives successful raw value/deep heap typing and all returned stable rows from genuine ProgramOutcome and the final administrative frame. `after_program_transition` keeps the original transition's same returned witness. |
| `CallableIndexedOwnedBodyRestorationAdmission` | `restore_rows`, `restore_fault_post` and `restore_post` retain the actual restored pool. `restore_return_with_post` uses the original restore action once and keeps its complete tuple plus successful post admission under genuine TypeContextSupports. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramPostAdmission` | `ResultAt` retains the original six effects, same returned State, Relates and PostAdmission. `ResultAt.at_value` exposes raw value typing and deep heap admission. The program/export P/R ports and `public_run_succeeded_reflects_program` consume their original proof producers once. |
| `SourceCoreChosenOrdinaryAcceptedOuterBodyLexicalExit` | `BodyResultWithExit` joins the original body result with genuine ReachedExit at the same final indices. `preserves_body_with_exit` / `reflects_body_with_exit` retain the actual binder, Source control and full supplied administrative environment. |
| `SourceCoreChosenOrdinaryAcceptedBodyStateExitReceipts` | `source_preserves_at_receipt` / `native_reflects_at_receipt` supply the existing strong PreparedNamedParameterReceipts contracts at the same actual Receipt. `source_bodies_for` / `native_bodies_for` quantify genuine strict body children without low erasure. |
| `SourceCoreChosenOrdinaryAcceptedPublicBodyExitReceipts` | `BodyAtReceiptWithExit` and `at_completed` retain one actual public parameter entry, the same initial state/Receipt/agreement and both strong body contracts for every independent grade. |
| `NamedInvocationFaultPostContracts` | `BodyExtra`, `TrivialExtra` and `ReturnedAtWithExtra` retain the same actual entry, parameter/body states, Source trace and restore receipt. `ReturnedAtWithExtra.forget` projects the original post-only receipt from those same witnesses. |
| `CallableIndexedOwnedInvocationBounds` | `SourceBodyAtWithExtra` / `NativeBodyAtWithExtra`, their continuation interfaces and `invocation_preserves_bounded_at_with_extra` / `invocation_reflects_bounded_at_with_extra` carry the supplied body fact and actual restored frame through the original core. Legacy post-only signatures remain unchanged. |
| `CallableIndexedOwnedPreparedNamedInvocationAdmission` | `source_body_with_extra_at_receipt` / `native_body_with_extra_at_receipt` and the actual continuation adapters retain strong Receipt exit/post at the same body state. `invocation_preserves_bounded_at_with_admission` / `invocation_reflects_bounded_at_with_admission` add caller post through pure restoration with genuine context support and saved rows. |
| `SourceCoreChosenOrdinaryAcceptedPublicInvocationExitAdmission` | `ResultAtWithExit`, `to_post`, `preserves_at_initial` / `reflects_at_initial` and `at_completed` retain the same causal body exit and restored caller post in the actual accepted initial/completed pair. |
| `CallableIndexedOwnedContextualStoredClosureAssociationReceipts` | `Member` retains genuine ordinary/principal formation authority. `selection`, `represents`, `association` and `extend` project or transport the same member. `formation_member` / `principal_formation_member` retain one original formation receipt. `Member.to_static` forwards it to the typed receipt at `350e4336`. |
| `CallableIndexedOwnedContextualInitializedClosureReceipts` | `StoredAt`, `allocate_initialized`, `read_member` and `callee_post` retain the positive member, real initialized cell reads and same reached state. `extend_with_reads` requires genuine future reads. `source_value_typed` / `post_admission` use actual Source admission. `TypedStoredAt` and `StoredAt.to_static` retain the same physical cells/reads with a typed StaticMember at `350e4336`. |
| `CallableIndexedOwnedContextualStoredMemberCallBounds` | `member_stage_origin`, `member_origin_at_caller`, `dispatch_at_member` and `callee_at_stored` derive the original gate and same-state callee post from a positive ordinary/principal member. `argument_rows`, `preserves_at_stored` and `reflects_at_stored` retain genuine ordered arguments, strict continuations and actual returned states. |
| `CallableIndexedOwnedContextualPrincipalStoredCallReceipts` | `member_from_selection`, `stored_from_selection` and `stage_origin_from_selection` retain method-principal authority and real current reads. `formation_member_from_selection` uses the original contextual principal formation once. |
| `CallableIndexedOwnedContextualStoredExpressionHeads` | `suffix_of_source` derives the original measured SourceSuffix; `Receipt`, `Head`, `LiveAt` and `LiveFor` bind real compiler and current-cell evidence. `preserves_at` / `reflects_at` supply admitted head contracts under genuine LiveFor and strict child continuations. |
| `CallableIndexedOwnedContextualStoredClosureWriteReceipts` | `written_member` performs one actual initialized write and retains the positive member at that cell. `preserves_other` requires genuine Source/native writes and map injectivity to preserve another cell. |
| `CallableIndexedOwnedContextualCellOrigins` (typed migration validated at `350e4336`) | `FunctionOrigins`, `PayloadOrigins` and `CellOrigins` retain typed StaticMember closure leaves through the existing payload/heap model. `payload_static_member` attaches genuine typed authority; the legacy `payload_member` forwards its receipt. `functions_include_general` forgets forward. Actual allocate/write ports and `stored_at` retain live cell evidence; `PostWithOrigins`, `post_at_same_state` and `at_value` bind admission and strong result at the same reached state. |
| `CallableIndexedOwnedContextualCellOriginFormationReceipts` (validated at `53095e76`) | `ordinary_formation` / `principal_formation` each retain one original formation and its receiving-model representation, same positive Member, unchanged strong heap, attached PayloadOrigins and result representation. |
| `CallableIndexedOwnedContextualCellOriginAllocationReceipts` (validated at `67d5c9af`) | `AdmissionWithOrigins`, `allocate_initialized_from_post` and `write_initialized_from_post` retain raw admission and positive cells inside the same actual reached witness. Allocation retains its full original tuple; a real mapped write preserves the actual records and stable rows. |
| `CallableIndexedOwnedStoredIndirectCallForModelReflection` (validated at `31b073bf`) | `application_reflects_of_bundles` derives the genuine receiving-model application leaf. `reflects_selected` reconstructs the whole finite Source call and retains its independent grade, represented result, heap and raw post at the same returned caller. Ordered bundles, Association and strict children remain genuine inputs. |
| `CallableIndexedOwnedContextualCalleeOriginReadReceipts` (typed migration validated at `350e4336`) | `InitializedReadAt` / `initialized_read_at` preserve the actual raw cell type and real reads. `CalleeAt` / `callable_at` and the closure/global/builtin projections retain positive origins through compatible wrappers; closure projections return the actual StaticMember; no selected-code or generalized-cell receipt is inferred. |
| `CallableIndexedOwnedContextualStoredCallOriginPosts` (validated at `1ec31128`) | `ResultAt`, `of_result_at`, `preserves_selected` and `reflects_selected` retain positive cells and raw admission inside the original same-state returned caller. `ResultAt.at_value` and `forget` observe or project that witness. Actual Association, ordered bundles, callee traces, SourceSuffix and strict children remain explicit. |
| `CallableIndexedOwnedContextualCellOriginExpressionPosts` (validated at `7e39da09`) | `model`, `PreservesAt` / `ReflectsAt`, `preserves_at` / `reflects_at` and both `forget` ports retain the original child witness with positive cells, result and admission. |
| `CallableIndexedOwnedContextualCellOriginReadPosts` (validated at `9308e009`) | `Reads`, `preserves_reads_at` / `reflects_reads_at`, `initialized_at_binding` / `initialized_at_local` and `callee_at_post` cover actual read branches and classify the same returned positive payload. |
| `CallableIndexedOwnedContextualTypedClosureReceipts` (validated at `df034b25`) | `Association` and `StaticMember` retain the actual ordinary/principal Code/body/Syntax. Compiler shape, native typing, stage origin, selection and forward representation ports retain that authority. `preserves_at` / `reflects_at` use genuine strict typed FlowBelow and the original invocation/restoration at the same Association. |
| `CallableIndexedOwnedContextualTypedClosureFormationReceipts` (validated at `1d279cc7`) | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` retain the same generated StaticMember, positive result/cells and Source admission. Each uses one original factory. Body and receiving registries remain separate; legacy `ResultAt.forget` requires their equality. |
| `CallableIndexedOwnedContextualStoredCallTypeReceipts` (validated at `7e85f0bb`) | `TypedCallAt`, `at_typed_callee` and `at_callee_post` derive ordered Source/native aggregate equalities from original raw typing, argument Tree, compiler callable policy and retained StaticMember. Admission and positive cells stay at the callee post; physical arity and stage verdicts remain separate. |
| `CallableIndexedOwnedContextualCalleeStageReceipts` (validated at `7e85f0bb`) | Origin and `boundary_at_*` ports retain the actual prepared user Dispatch or builtin row. `BuiltinAt.parameter_count`, `first_gate` and `resolve_prefix` retain the physical builtin count, native `.inRight .word .unit` first-gate result and unchanged original suffix/state/strict grade. Whole call/body composition remains separate. |
| `CallableIndexedOwnedPreparedOrdinaryBodyProjection` (validated at `0451cd62`) | `bodyWith`, `plain`, `Receipt` and `StaticMember` retain the same prepared JointBody. Flow ports use its real table and reached interpretations; `forget` and `extend` preserve the retained authority. |
| `CallableIndexedOwnedPreparedPrincipalLambdaSupport` (validated at `0451cd62`) | `Support`, `PreparedAt`, `source_receipt` and `Receipt` retain the selected Principal Site, implementation, dictionary and cached compilation. Same-body flow and forward plain/provenance ports keep those indices. |
| `CallableIndexedOwnedPreparedPrincipalFormationReceipts` (validated at `0451cd62`) | `formation_member` and `formation_post` retain one original principal formation, its prepared receipt and the same reached positive post. |
| `CallableIndexedOwnedPreparedContextualCellOrigins` (validated at `0451cd62`) | `Association`, `StaticMember`, `PayloadOrigins`, `CellOrigins` and `StoredAt` keep actual preparation through growth, allocation, writes and reads. `PostWithOrigins` retains that authority and Source admission at the same reached state. |
| `CallableIndexedOwnedPreparedContextualFormationReceipts` (validated at `0451cd62`) | Ordinary/principal `formation_member` and `formation_post` use the real factory once and retain the prepared member, positive cells and Source admission without equating body and receiving registries. |
| `CallableIndexedOwnedPreparedContextualFunctionViews` (validated at `0451cd62`) | `functions_include_general`, `observations`, `runtime_views`, `payload_general` and `cells_general` expose the forward General views. |
| `CallableIndexedOwnedPreparedContextualFormationBounds` (validated at `0451cd62`) | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` retain value/fault alternatives, prepared cells and admission at the returned state with independent Source/native grades. |
| `CallableIndexedOwnedPreparedCompilerChildCollector` (validated at `e27c3ccb`) | `Collected`, `factories`, `caller`, `prepared`, `cover_for` and `cover` retain actual ordinary compiler children and derive their coverage. |
| `CallableIndexedOwnedPreparedContextualQualification` (validated at `e27c3ccb`) | `Facet`, qualified Association/StaticMember and function/payload/cell origins retain one concrete preparation qualification through forward extension. |
| `CallableIndexedOwnedPreparedPrincipalCompilerChildren` (validated at `e27c3ccb`) | Accepted children, `SiteShell`, `extraction`, `collected` and `root_of_accepted` retain the selected method/dictionary and invoke the original joint-body producer once at the same Site. |
| `CallableIndexedOwnedPreparedCompiledQualification` (validated at `e27c3ccb`) | Positive `Ordinary`/`Principal` constructors, `facet` and association producers install the actual collected compiler packet at the same Code and Support. |
| `SourceCoreChosenOrdinaryAcceptedPublicRootExitAdmission` (validated at `6bbea5e`) | `RootAtInitialWithExit`, `forget`, `invocation_at_session`, `at_session`, `preserves_root` and `reflects_root` retain the same causal exit/admission witness at actual root completion, including the measured native invocation child and independent Source grade. |
| `SourceCoreChosenOrdinaryAcceptedPublicProgramOutcomeWithExit` (validated at `6bbea5e`) | `ProgramAtWithExit`, `forget`, `at_started` and the `*_with_exit` program/export ports join that same result to genuine ProgramOutcome and successful Word export through the original receipts. |

The literal invocation derives its body ledger and runtime validity from the same selected Support. Source and native grades remain independent. The approved body child is literal occurrence 3; the outer indirect parent at occurrence 5 remains in the Source. Whole parent preservation and reflection now derive the callee post, pair arguments, fault exclusion, dispatch and native argument bundle internally. Both retain the actual returned caller and cumulative heap, mapping, world and administrative effects. Genuine initial heap, stored-cell authority, captures, history, environment correspondence, native typing and input admission remain explicit in the parent ports. The accepted outer body now forms its initializer and allocates its local cell once, then runs the proved parent at that actual admitted post. Reflection reconstructs whole native execution and uses determinism to align its final value and store. The returned result retains cumulative effects, the actual restored pool, every ordered row and successful raw value/deep heap typing at Γ0. The BodyState adapter derives these inputs from the same actual named parameter Receipt and runs each whole-body port once. Its returned result retains the same actual pool and successful raw PostAdmission. The existing low SourceBodyAt and NativeBodyAt interfaces remain available. The new BodyStateExitReceipts companion also populates PreparedNamedParameterReceipts.PreservesAt/ReflectsAt with genuine ReachedExit, successful PostAdmission and the same returned state.

The latest committed and normally verified code commit is `2caef32a`. The typed contextual receipt unit was introduced at `df034b25`, and the positive-cell backend migrated at `350e4336`. `CallableIndexedOwnedContextualTypedClosureReceipts` retains actual ordinary and method-principal lambda formation through a typed `Association` and a propositional `StaticMember`.

The receipt keeps the original Code, owner, ordered history, captures, parameter bindings, static body and independent Source syntax. Its forward representation and selection ports preserve that authority. Finite application preservation and reflection consume real argument typing, initial stable rows and strict typed `FlowBelow` for the same retained Code. Each uses the original parameter/body invocation and saved caller restoration once, retaining the actual returned pool and independent Source/native grades. The typed finish derives exclusion of escaping break/continue from the Source body receipt; it requires no unconditional escaped-control diagnostic at internal Word zero.

Normal verification at `df034b25` passes 5635 registered build jobs, one empty strict Source log, all 56 complete module-owned declarations and 24 API checks. Every private/normal TYPE/AXIOMS block and the complete API logs match literally, using only the standard three axioms. The measured cumulative census is 16605 from 16549: 56 additions, no prior overlaps or removals. The 5567-row pre-install snapshot, actual 2094-module import environment, one existing `CoreLowering` object delta, three-module dependency cone/rebuild and all 4985 protected artifacts pass. Three proof-port name corrections preceded the final empty strict log. This unit adds one proof Source and one umbrella import.

The positive-cell proof backend migrated to these receipts at `350e4336`. Four strict Source logs are empty on their first attempts. Normal validation passes all 92 complete private/normal literal TYPE/AXIOMS blocks and 22 byte-exact API checks. The original/current ownership census changes 88 → 92: 80 same-name literal matches, eight explicitly reviewed TYPE changes, four additions and no removals. Seven changes replace the legacy `Member` with `StaticMember`; one replaces `StoredAt` with `TypedStoredAt`. The measured cumulative declaration census is 16609 from 16605. Build 5635, the 5568-row pre-install snapshot, actual 2110-module import environment, 11 existing object deltas covered by the 15-module dependency cone/rebuild, and all 4985 protected artifacts pass. Shared registration roots and imports remain exact.

Typed closure formation now preserves and reflects ordinary and method-principal heads at `1d279cc7`. `CallableIndexedOwnedContextualTypedClosureFormationReceipts` keeps the generated `StaticMember`, positive cells and raw Source admission inside the same returned state witness. Each direction uses its original formation factory once. Reflection uses native determinism and independently sizes the Source trace. The main results keep the body registry and receiving registry separate; the two legacy `ResultAt.forget` ports explicitly require their equality because their targets use one registry.

Normal verification passes 5636 registered build jobs, one empty strict Source log, all 10 complete module-owned declarations and eight API checks. Private/normal TYPE/AXIOMS blocks and complete API logs match literally. The cumulative census is 16619 from 16609: ten additions, no overlaps or removals. The 5568-row pre-install snapshot, actual 2110-module environment, one existing umbrella object delta, three-module dependency cone/rebuild and all 4985 protected artifacts pass. The unit adds one proof Source and one umbrella import. Mixed expression/body closure and all-pass composition remain incomplete.

Typed stored-call and selected stage-boundary receipts now pass normal verification at `7e85f0bb`. `CallableIndexedOwnedContextualStoredCallTypeReceipts` derives ordered Source/native aggregate equalities from the original compiler receipt, raw Source typing, argument Tree and the positive callee's retained StaticMember. `at_callee_post` keeps Source admission and positive cells at that same reached state. Body and receiving registries remain separate. Physical binder arity and stage decisions require their own receipts.

`CallableIndexedOwnedContextualCalleeStageReceipts` uses the retained origin and actual caller preparation to construct a user Dispatch or authentic builtin row. `BuiltinAt.parameter_count` retains the builtin's physical parameter-list length. Its absent guard proves the original first-gate result `.inRight .word .unit`; `resolve_prefix` preserves the original argument/application suffix, unchanged gate store and strict suffix grade. User rejection, second-gate arity/application and whole indirect body composition remain separate.

Normal verification passes 5638 registered build jobs, two empty final strict Source logs, all 47 complete module-owned declarations (22 typed-call / 25 stage-boundary) and 17 API checks. Private/normal TYPE/AXIOMS blocks and complete API logs match literally. The cumulative census is 16666 from 16619: 47 additions, no overlaps or removals. The 5569-row pre-install snapshot, actual 2126-module environment, one existing umbrella object delta, four-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds two proof Sources and two umbrella imports.

Prepared closure receipts and cell origins now pass normal verification at `0451cd62`. Ordinary and selected-principal support retain the actual compiler preparation, one JointBody, the same Code and typed body, and Source provenance. Principal support also retains the selected implementation, dictionary and cached named compilation. These receipts project forward to the existing typed model; an existing plain leaf cannot be upgraded to prepared authority.

The prepared Association, payload and cell model preserve that authority through map/world growth and actual allocation, writes and reads. Formation uses its original ordinary or principal factory once and retains the prepared member, represented result, positive cells and Source admission at the same reached state. Graded preservation and reflection retain the Source value/fault alternatives and independent Source/native grades. The body's static registry and receiving registry remain separate; function observations and runtime views project forward to the General model.

Normal verification passes one registered build with 5645 jobs, seven empty final strict Source logs, all 274 module-owned declarations and 79 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 16666 to 16940: 274 additions, no overlaps or removals. The 5571-row pre-install snapshot, actual 2172-module environment, one existing umbrella object delta, nine-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds seven proof Sources and seven umbrella imports.

Compiler child collectors and prepared function qualification now pass normal verification at `e27c3ccb`. The ordinary collector derives child coverage from the actual retained compiler inventory. The selected-principal collector keeps the actual method, dictionary, cached compilation and same Site; its original joint-body producer runs once. Concrete ordinary/principal qualification travels with the same Code and Support through function values, payloads and cells, including forward map/world extension. These static receipts retain compiler authority for the subsequent semantic proof.

Normal verification passes one registered build with 5649 jobs, four empty final strict Source logs, all 159 module-owned declarations and 36 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 16940 to 17099: 159 additions, no overlaps or removals. The 5578-row pre-install snapshot, actual 2187-module environment, 1 existing umbrella object delta, 6-module dependency cone/rebuild and all 4985 protected artifacts pass. The code commit adds four proof Sources and four umbrella imports.

Canonical parameter protocols and qualified closure flow now pass normal verification at `0338a276`. Ordinary and selected-principal packet producers retain the original parameter entry, canonical bindings, globals and base pool. Typed continuations consume the body flow under that same caller protocol and keep the original Source body receipt. Qualified formation retains compiler authority with the represented closure, positive cells and Source admission. The canonical flow producer uses one retained JointBody and transports the actual returned pool through its protocol bridge. Source and native grades remain independent.

Normal verification passes one registered build with 5655 jobs, six empty strict Source logs, all 128 module-owned declarations and 29 API checks. Complete private/normal TYPE/AXIOMS blocks and API logs match literally, using only the standard three axioms. The cumulative census grows from 17099 to 17227: 128 additions, no overlaps or removals. The 5582-row pre-install snapshot, actual 2192-module environment, one existing umbrella object delta, eight-module dependency cone/rebuild and all 4985 protected artifacts pass. Six proof Sources and six umbrella imports are added.

Protocol-specific finish, ordinary/principal parameter packets, qualified formation and canonical flow are integrated. The shared expression/body family still needs actual compiler occurrence typing, canonical capture and selected method-prefix alignment, reached diagnostic interpretations, and a concrete common induction over expressions and function bodies. The canonical flow producer requires genuine diagnostic table readiness and both reached error interpretations; registry extension alone supplies neither. Named and indirect dispatch, mixed bodies and the final public theorem across specialization, evidence and comptime remain unfinished.

Reached read and index diagnostics are integrated at `ef85a057`. The proof uses the actual local-cell read or raw missing-index witness, the selected compiler issuer and the receiving public decoder. The ordered Source prefix, diagnostic reason, returned state and independent grades remain attached to that occurrence. Normal verification passes build 5673, seven empty strict logs, 76 declarations and 24 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17536.

Direct prepared closure origins and ordinary/principal formation are integrated at `6dbfa243`. The actual Code, History, Support, Source origin, captures and positive cells remain together in the returned state. The stage-scope receipts recover the original owner and source scope from authentic sidecars. Receiving and body registries remain independent. Normal verification passes build 5677, four empty strict logs, 139 declarations and 47 API checks with complete literal private/normal agreement; the cumulative census is 17675. Invocation adapters and the shared expression/body family still need normal integration and complete compiler occurrence factories.

Paired compiler typing and constructive call packets are integrated at `2caef32a`. One compiler traversal retains independent actual-context and fixed-prefix typing for each used child, while keeping the original body Tree, plan and diagnostic issuer. Accepted closure and named branches construct their argument packets from genuine Source types, physical arity and the selected owner or dictionary. Eligible ordinary and principal lambda flow uses the same retained compiler receipt and receiving state. Normal verification passes build 5742, 20 empty strict logs, 273 declarations and 75 API checks with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 18887 (+273, no overlaps or removals). The numeric expression/body induction and complete public compiler coverage remain unfinished.

The shared expression/body family remains incomplete. Static factories must construct the same retained body's compiler Tree at every genuine occurrence context, scope and read budget. Source typing alone does not justify globally empty evidence or coercions, or exclude generalized local cells. Actual compiler alternatives require their own coverage. Ordinary execution also needs authentic guard acceptance at each reached indirect call; separate staged judgments preserve guard rejection before arguments. The final recursive staging proof must cover the remaining Source forms.

Next: close one receiving-model expression/body family across closure, named/global, builtin and method calls, with positive cells and genuine physical arity, Source stage gates and public diagnostic inclusion. Then compose the actual specialization, evidence and comptime transformations through the public compilation and input boundary. Generalized/scheme cells, compound assignment, general failure/export-error correspondence and the final all-pass theorem remain incomplete. The first objective remains 100%; the second stays about 70%, and the equally weighted overall estimate stays about 85%. These are estimates of completed work, not declaration counts or remaining time.

The actual public Recipe and completed bootstrap populate the named parameter Receipt and its ContinuationAgreement for the unchanged accepted fixture. `PublicBodyCorrespondence.at_completed` supplies admitted body preservation/reflection and SourceBodyAt/NativeBodyAt. `PublicInvocation.at_completed` supplies original named invocation at the same initialization store, deriving its actual parameter child internally and retaining caller restoration and cumulative effects. That low ResultAt remains available. The accepted public program companion adds successful raw PostAdmission at the same returned caller using genuine ProgramOutcome, saved stable rows and the final administrative frame.

The Session consumer retains one real `openWithReceipt` / `bootstrapFreshWithReceipt` / `resume` chain and the actual `.ready` equation. The program collector derives StaticReceipt on that same fixture, performs its selected root start once and calls `resumeWithReceipt` once. Its successful public result has the identical Source Word and genuine original ProgramOutcome. The post-admission companion now retains successful raw value/deep heap typing and all returned stable rows at that result's same caller state. Faults retain stable rows only. Source and native budgets remain independent; Source Word export requires a positive boundary budget. The finite accepted body retains genuine ReachedExit/LexicalResult through the strong parameter Receipt contract. The generic invocation factor now carries a supplied body fact inside the same causal witness through one original caller restoration. The adapter now supplies that fact from genuine strong Receipt contracts and adds caller admission at the same causal witness using pure restoration and genuine context support. Its accepted initial/completed pair retains both directions without replaying bootstrap or parameters. At `06f2635c`, normal verification passes build 5618, full 27 / API 20, two empty strict logs and every private/normal TYPE/AXIOMS block literally; cumulative 16297 adds 27 names with no overlaps or removals. The 5549-row snapshot, 2295-module environment, two existing object deltas, four-module cone/rebuild and 4985 protected artifacts pass. The public root/program exit companions now retain the same causal exit/admission result at actual root completion and successful positive Word export. They use the original start/resume receipts, retain the measured native invocation child and independent Source grade, and project low observations by pure forgetting. At `6bbea5e`, normal verification passes build 5620, full 31 / API 14 and two empty strict logs; all 31 private/normal TYPE/AXIOMS blocks match literally with only the standard three axioms. Cumulative 16328 adds 31 names to 16297 with no overlaps or removals. The 5551-row snapshot, 2297-module environment, one existing `Tests.Main` object delta, three-module cone/rebuild and 4985 protected artifacts pass. The proof umbrella is unchanged and no IO is added. The scope is the finite accepted fixture. Contextual ordinary/principal members now pass through initialized allocation/read to Association and the same-state callee post at `d51edb70`. The common stored-call ports at `45a38df8` connect that producer to the original selected-call preservation/reflection. The admitted whole-expression head now derives its SourceSuffix internally; universal LiveFor and mixed-family closure remain separate. General public failure/export-error correspondence, mixed bodies and all-pass correctness remain unfinished. At `8d2289c5`, normal verification passed 5616 build jobs, two empty strict Source logs, all 62 private/normal literal TYPE/AXIOMS blocks and 36 signatures. The measured cumulative count is 16270 (net +10); 50 original same-name blocks match literally and two generated helpers have reviewed moves. This factor adds no runner or IO. The public Word 7 and two existing regression receipts at `7b0f562f` remain historical.

The accepted initialized body now preserves and reflects genuine lexical exit and LexicalResult with the same represented result, cumulative effects, returned pool and PostAdmission. The BodyState adapter uses the actual parameter Receipt's full administrative environment; creator capture remains separate. One public parameter entry supplies the same initial state, Receipt and ContinuationAgreement and both strong body contracts at independent grades.

The three-module checkpoint is `f0274543`. Its one prior overlap is `Tests.SourceCoreChosenOrdinaryAcceptedBodyStatePorts.captures_at_entry.congr_simp`, whose saved-before and current TYPE/AXIOMS blocks match literally. The proofs add no runtime action, runner or new public Session correspondence.

The old `SourceTypedRuntime` namespace remains in compatibility value, observation, and validation carriers. Its name does not imply that a runtime evaluator of Source expressions and statements remains.

Moving the comptime evaluator to Core and adding source contract/storage/external-call connections are the agreed next phase. Meaning preservation for comptime transformations actually performed by the current compiler is part of the second goal.

## Canonical parameter and closure proof interfaces (`0338a276`)

These interfaces retain static proof authority for the existing public execution API.

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedTypedLambdaProtocolContinuations` | `Packets`, `FlowPreserves`, `FlowReflects`, `source_continuation`, `native_continuation` |
| `CallableIndexedOwnedPreparedLambdaProtocolPackets` | `Ordinary.packets`, `Principal.packets` |
| `CallableIndexedOwnedPreparedQualifiedExpressionOutputs` | `payload_static_member`, `closure_member`, `Post` |
| `CallableIndexedOwnedPreparedQualifiedFormationReceipts` | Ordinary/principal `formation_member` and `formation_post` |
| `CallableIndexedOwnedPreparedQualifiedFormationBounds` | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` |
| `CallableIndexedOwnedPreparedCanonicalFlowBounds` | `Origin`, its protocol/bridge/transport/bindings/producer/acquire ports, `preserves_flow`, `reflects_flow` |

Protocol-specific finish, ordinary/principal parameter packets, qualified formation and canonical flow are integrated. The shared expression/body family still needs actual compiler occurrence typing, canonical capture and selected method-prefix alignment, reached diagnostic interpretations, and a concrete common induction over expressions and function bodies. The canonical flow producer requires genuine diagnostic table readiness and both reached error interpretations; registry extension alone supplies neither. Named and indirect dispatch, mixed bodies and the final public theorem across specialization, evidence and comptime remain unfinished.

## Native compiler occurrence proof interfaces (`e0edb2ec`)

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedPreparedCanonicalCaptureReceipts` | Prefix/capture agreement and ordinary/principal captured parameter packets and admission |
| `CallableIndexedOwnedPreparedPrincipalRootPrefixTyping` | `body_native_at_prefix` |
| `CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping` | Snapshot result normalization and `certificate_native` |
| `CallableIndexedOwnedPreparedNativeLexicalCollectors` | `tree_of_typed_flow_with_residual` |
| `CallableIndexedOwnedPreparedNativeMatchCollectors` | Native expression/body extraction and `finite_typed_of_lower` |
| `CallableIndexedOwnedPreparedNativeAssignmentChildren` | Raw typing, packed children, present RHS and ordered key extraction |
| `CallableIndexedOwnedPreparedNativeAssignmentHeadCollectors` | `Head.of_lower_with_raw_occurrences` |
| `CallableIndexedOwnedPreparedNativeForHeaderCollectors` | `extraction_of_lowerForItems_with_coupled` |
| `CallableIndexedOwnedPreparedNativeImperativeCollectors` | `extraction_of_typed_position_with_catalog_coupled` |

These interfaces derive local child typing from the same emitted Core expression. Authentic Source facts and the actual compiler Site remain independent inputs. The shared expression/body induction and full public compiler theorem remain incomplete. Normal verification passes build 5664, nine empty strict logs, 134 declarations and 28 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17361.

## Static compiler authority proof interfaces (`27abbb6f`)

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedLocalIdentityFreshness` | `lambda_parameter_not_input`, `lambda_parameter_kind`, `lowered_parameter_kinds`, `match_hidden_fresh` |
| `CallableIndexedOwnedPreparedNativeSitePolicies` | Same-Site match context, binder/read/reference-slot/allocator policies and actual issued assignment/unary policies |

These interfaces derive static facts from genuine Source ownership and one actual Named Compilation and Site. They retain the root policy, scope/ledger and actual issued diagnostic identities. Runtime validity alone does not establish ownership, and these interfaces do not assume or prove the shared body execution family. Normal verification passes build 5666, two empty strict logs, 99 declarations and 16 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17460. The complete compiler theorem remains in progress.

## Reached diagnostic proof interfaces (`ef85a057`)

| Module | Main interface |
| --- | --- |
| `CallableIndexedOwnedPublicDecodedAssignmentFaults` | `ErrorView`, `faults`, `of_decoded`, `reached_interpretation` |
| `CallableIndexedOwnedSelectedDiagnosticIssuerReceipts` | `lowered`, `selected_collected`, `SelectedReceipt`, `at_selected`, `at_principal`, `SelectedReceipt.principal`, `SelectedReceipt.principal_source` |
| `CallableIndexedOwnedReachedExpressionDiagnosticBounds` | `preserves_with_literals`, `reflects_with_literals` |
| `CallableIndexedOwnedReachedDataHeadBounds` | `Head.preserves_at`, `Head.reflects_raw_at` |
| `CallableIndexedOwnedReachedAdmittedDataHeadBounds` | `preserves_at`, `reflects_at` |
| `CallableIndexedOwnedReachedAdmittedExpressionCallsHeads` | `preserves_at_with_calls`, `reflects_at_with_calls` |
| `CallableIndexedOwnedSelectedReadIndexDiagnosticPolicies` | `reasonAt`, `reason_eq`, `own_found`, `reads`, `missing` |

These interfaces keep actual reached read/index witnesses and the selected receiving diagnostic issuer. They construct decoder error views from real runtime facts and retain the original Source prefix, state and grades. Header reason alignment, compiler branch factories, strict expression/body induction and the full public compilation theorem remain open. Normal verification passes build 5673, seven empty strict logs, 76 declarations and 24 API checks, with literal private/normal TYPE/AXIOMS and API agreement; the cumulative census is 17536.

## Direct prepared closure proof interfaces (`6dbfa243`)

| Module | Main interfaces |
| --- | --- |
| `CallableIndexedOwnedPreparedNativeDirectCellOrigins` | `Association`, `StaticMember`, `FunctionOrigins`, `PayloadOrigins`, `CellOrigins`, `Post`, forward representation and runtime views |
| `CallableIndexedOwnedPreparedDirectFormationReceipts` | Ordinary/principal `history_at`, `formation_member` and `formation_post` |
| `CallableIndexedOwnedPreparedDirectFormationBounds` | Ordinary/principal `ResultAt`, `preserves_at` and `reflects_at` |
| `CallableIndexedOwnedPreparedDirectStageScopeReceipts` | `sidecar_owner`, `code_scope`, `scope_at` and `original_scope` |

These interfaces retain the actual prepared source, captures and returned state. They recover the original stage scope without assuming its guard result. Body and receiving registries are independent. Normal verification passes build 5677, four empty strict logs, 139 declarations and 47 API checks with complete literal private/normal agreement; the cumulative census is 17675. The strict mixed expression/body family, full compiler alternatives and the final public theorem remain unfinished.

## Selected named static proof interfaces (`ee27dc50`)

| Module | Main interfaces |
| --- | --- |
| `CallableIndexedOwnedSelectedNamedHeaderReceipts` | `diagnostic_typed`, `reissued`, `reissued_view`, `reason_at`, `canonical_at_prepared`, `retained_at_prepared` |
| `CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts` | `selected_evidence_empty`, `SourceReceiptCover`, `SourceReceiptCover.selected_empty` |
| `CallableIndexedOwnedPreparedNamedSourceFactoryFacts` | `source_types`, `selected_validity` |
| `CallableIndexedOwnedNamedPhysicalArityReceipts` | `bound_parameters`, `dispatch_parameter_count`, `named_parameter_count`, `before_application` |

These factories retain the same actual selected row, diagnostic issuer, complete ordered Source metadata and resolved dictionary. Ordinary selected dictionary emptiness and physical arity follow from authentic receipts. Arity does not establish acceptance of the separate staging guard. The finite Source receipt cover remains an input; constructing that inventory, closing the shared expression/body induction and covering all public compiler branches remain unfinished.

## Prepared named inventory and bootstrap interfaces (`ae3d5594`)

| Module | Main interfaces |
| --- | --- |
| `CallableIndexedOwnedPreparedFiniteNamedInventories` | `Input.of_selected`, `issue`, `headers`, `globals`, `source_receipts`, `ordered`, `reached_coverage` |
| `CallableIndexedOwnedPreparedNamedDiagnosticSources` | `prepared`, `source`, `issuer`, `assignments`, `operand`, `unary`, `projection`, `missing`, `factory` |
| `CallableIndexedOwnedPreparedDirectNamedProfileExtraction` | `Children`, `Receipt`, `extract_at`, `Receipt.profile` |
| `CallableIndexedOwnedPreparedCatalogNamedProfiles` | `Profile.nested`, `Profile.receiving`, `Profile.factory`, `Profile.prepared_eliminator` |
| `CallableIndexedOwnedPreparedCatalogNamedBodyContinuations` | `body_protocol`, `bridge`, `source_continuation`, `native_continuation` |
| `CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds` | `invocation_preserves_bounded`, `invocation_reflects_bounded`, `application_preserves_at`, `application_reflects_at`, `source_certificate`, `arguments_at_global` |
| `CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles` | `of_collected`, `extract_at` |
| `CallableIndexedOwnedNamedBootstrapReceipts` | `of_recipe`, `Bootstrap`, `NamedOwner`, `NamedOwner.capture_zero`, `NamedOwner.globals`, `NamedOwner.named_capture` |
| `CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts` | `slots`, `empty_locals`, `cache`, `ledger`, `of_recipe` |
| `CallableIndexedOwnedReachedNamedRangeReceipts` | `range_of_valid_match`, `range_of_selected`, `range_at_catalog`, `catalog_range_of_selected` |

Direct and nested typed named-body adapters retain the same actual parameter-entry protocol. A bootstrap owner is produced from initialization and transported forward through a complete key embedding. An arbitrary existing named capture cannot be upgraded to that provenance. Profiles, genuine child typing, receiving diagnostics and the common graded expression/body induction must still be supplied by their actual compiler producers.

## Shared positive function and native call proof interfaces (`922ac60f`)

The following modules are registered through `CoreLowering`. Their interfaces retain the actual owner, compiler association, Source dictionary and occurrence context.

| Module suffix | Main interfaces |
| --- | --- |
| `PreparedPositiveFunctionOrigins` | `Owner`, `OwnerCover`, `ClosureAssociation`, `NamedAssociation`, `PayloadOrigins`, `CellOrigins`, `closure_member`, `global_member`, `bootstrap_owner_cover` |
| `PreparedFunctionModelFormationBounds` | Ordinary and principal `preserves_at` / `reflects_at` |
| `PreparedSelectedNativeFamilyQualification` | `facet`, `ordinary_family`, `principal_family`, `ordinary_prepared`, `principal_prepared` |
| `PreparedNativeTaggedLambdaCompilerReceipts` | `of_certificate_with_shell_property` |
| `PreparedReachedNativeExpressionTreeBounds` | `RuntimeTree`, `preserves_at`, `reflects_at` |
| `PreparedCatalogTypedNamedCallBounds` | `preserves_at`, `reflects_at`, `CallerEvidence`, `preserves_calls`, `reflects_calls` |
| `PreparedCatalogIndirectInvocationDispatcher` | `Receipt`, `preserves`, `reflects` |
| `PreparedCatalogIndirectArgumentReceipts` | `closure`, `named` |
| `PreparedCatalogIndirectApplicationBounds` | `ArgumentPackets`, `preserves`, `reflects` |
| `PreparedNamedProfileFamilies` | `profiles`, `source_continuation`, `native_continuation` |

These are conditional proof interfaces. A concrete packet producer must establish accepted physical argument count, retained Source typing and the selected callee association at the actual argument post. The shared expression/body induction must then supply the strict body continuations. These interfaces do not yet constitute the final theorem for all compiler passes.


## Paired compiler typing and accepted call interfaces (`2caef32a`)

These interfaces retain the same compiler occurrence, issuer and reached caller.

| Module suffix | Main interfaces |
| --- | --- |
| `IndirectSourceTypeRows` / `AcceptedIndirectPhysicalArity` | `original_rows`, `selected_count`, `closure_count`, `named_count` |
| `PreparedAcceptedClosureArgumentPackets` | `packets` |
| `PreparedAcceptedNamedArgumentPackets` | `StaticBodies`, `at_arguments`, `packets` |
| `PreparedPositiveNamedValueReceipts` | `association`, `of_read`, `at_arguments` |
| `PreparedPairedReachedNativeExpressionTreeBounds` | `NativeAt`, `WithBoth`, `native_head`, `RuntimeTree`, `preserves_at`, `reflects_at` |
| `PreparedPairedNativeLexicalCollectors` / `PreparedPairedNativeMatchCollectors` / `PreparedPairedNativeImperativeCollectors` | Single extraction with both actual and fixed native child witnesses |
| `PreparedPairedNamedProfileExtraction` | `Children`, `body_native_at_prefix`, `extract_at` |
| `PreparedEligibleSelectedNativeFamilyFlowStep` / `PreparedEligibleSelectedAssociationFlowBounds` | Ordinary/principal receiving flow and strict bounds at eligible roots |
| `PreparedSelectedPositiveLambdaPackets` / `PreparedEligibleSelectedLambdaCallBounds` | `of_compiler`, `Point`, ordinary/principal preservation and reflection |
| `PreparedPositiveCalleeBoundaryReceipts` | `function_origin`, `payload_origin`, `boundary_at_payload` |

The argument factories discharge concrete packet and arity obligations at accepted call branches. The eligible body ports still require the numeric expression/body induction. Reached stage rejection remains an independent Source staging outcome before argument evaluation; a boundary receipt does not establish complete recursive staging coverage.

## Accepted indirect parent and eligible function interfaces (`22a68060`)

Accepted-call proofs construct the builtin or user argument packet at the actual argument post, then invoke the original application and restore the saved caller. The following modules are registered through `CoreLowering`.

| Module suffix | Main interfaces |
| --- | --- |
| `PreparedOriginGlobalsCarriers` | `carrier`, `forget_slots` |
| `PreparedPairedCatalogNamedProfileFamilies` | `profiles` at the actual body entry with both native typings |
| `PreparedHeaderRootPolicyReceipts` | `header_action`, `at_successor`, `at_accepted` |
| `PreparedAcceptedBuiltinArgumentPackets` | `builtin_member`, `at_arguments`, `packets` |
| `PreparedAcceptedBuiltinIndirectParentBounds` | `preserves`, `reflects` |
| `PreparedAcceptedUserIndirectParentBounds` | `UserCallee`, closure/global constructors, `user_packets`, `preserves`, `reflects` |
| `PreparedIndirectCalleeReflection` | `reflects_value`, `reflects_fault` |
| `PreparedPairedOriginNamedCallBounds` | `preserves_calls`, `reflects_calls` |
| `PreparedEligiblePairedExpressionFamilies` | Pointwise and budgeted `ExpressionPreserves` / `ExpressionReflects`, `preserves_at_prefix`, `reflects_at_prefix` |
| `PreparedEligibleSelectedLambdaRecipes` | `RawLambda`, ordinary/principal `CompilerInputs`, `Recipes`, `preserves_at`, `reflects_at` |

Builtin application closes through the original primitive proof. User application retains strict closure or named body hypotheses. The eligible expression interfaces describe the needed induction hypotheses; they do not close the numeric expression/body induction. Actual first- and second-stage acceptance remain explicit. A rejected first-stage guard retains its separate Source staging judgment before arguments. Second-stage rejection occurs after argument evaluation and remains a separate pending branch. Complete scoped rejection and compiler occurrence coverage remain unfinished.

## Staged indirect call runtime proof interfaces (`d9f2a0c4`; 2026-10-10)

The ten proof Sources below are registered through CoreLowering at `d9f2a0c4`. Normal validation checked all 234 owned declarations and 71 selected APIs with literal private/normal TYPE/AXIOMS and complete API agreement. Build 5762 passed and the cumulative census grew from 19016 to 19250. Each Source had two nonauthor reviews. The common public execution API and Core AST/runtime definitions retain their existing behavior.

Except for `Staging.RecursiveTraceSize`, module names below are suffixes under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `Staging.RecursiveTraceSize` | `Size.stepSize`, `stepSize_positive`, `child_lt_stepSize`; `Expression`, `Expressions`, `Applies`, `Statements`: each `sound`, `of_trace` (11) | Grades the 46 original supported recursive staging rules; preserves actual scope, heap and failure tag. |
| `PreparedPairedSelectedAssociationFlowBounds` | `preserves_at_most`, `preserves_below`, `reflects_below` (3) | Same retained Association and literal fixed-prefix specialization; numeric eligible E and receiving contracts remain inputs. |
| `PreparedNamedEligibleExpressionFlowBounds` | `Certificate`, `certificates`, `Static`, `children`, `of_collected`, `preserves_children`, `reflects_children`, `preserves_flow`, `reflects_flow` (9) | Same finite Issued packet, actual Header root and independent actual/fixed typing; requires strict eligible E and static/receiving receipts. |
| `PreparedFunctionModelStageReflection` | `reflects_rejected` (1) | Actual rejected first gate before arguments, at the genuine callee post and full receiving function model; retains supplied genuine callee trace. |
| `AdmittedStagedExpressionBounds` | `PostAdmission`, `PostAdmission.at_value`, `PostAdmission.rows`, `PostAdmission.at_fault_type`, `after_expression_sized`, `after_related_expression_sized`, `PreservesAt`, `ReflectsAt`, `PreservesAtMost`, `PreservesBelow`, `ReflectsBelow` (11) | Actual reached caller state, relation and administrative frame; deep Source admission follows successful values, and stage failure retains stable rows. |
| `PreparedStagedIndirectCalleeFaultBounds` | `ResultAt`, `preserves_callee_fault`, `reflects_callee_fault` (3) | Propagates the exact semantic or nested stage failure from a strict callee child, preserving reached heap/store and caller relation. |
| `PreparedScopedCallBoundaryReceipts` | `CallView`, `CallView.argument_count`, `substituted_indirect_origin`, `indirect_origin`, `boundary_at_original`, `boundary_at_source_view` (6) | Forward original-call transport from the same SourceView and Prepared row; original codebook metadata stays distinct from actual substituted metadata. |
| `PreparedSecondCallGateRejection` | `rejected_row`, `rejected_gate`, `closure_gate`, `named_gate`, `builtin_gate`, `values_count`, `closure_source`, `named_source`, `builtin_source`, `user_native_preserves`, `user_native_completion`, `builtin_native_preserves`, `builtin_native_completion`, `arityFaults`, `stagedArityFaults`, `public_diagnostic`, `public_argument_post`, `public_staged_argument_post` (18) | Actual selected physical arity and codebook row yield semantic arity failure after evaluated arguments; retains reached argument state and explicit receiving transport. |
| `AdmittedStagedExpressionSequence` | `PostAdmission`, `PostAdmission.at_values`, `preserves_values`, `preserves_fault`, `reflects` (5) | Constructive ordered argument fold from genuine Tree, unique/typing rows and strict staged child E; success-only admission, exact failures and cumulative effects. |
| `PreparedStagedIndirectNativePrefix` | `CalleePost`, `FaultPrefix`, `ValuePrefix`, `reflects_prefix` (4) | Actual whole-parent first-bind inversion yields strict callee completion, its Source trace and reached post, then fault propagation or the original gate suffix. |

These are conditional semantic ports. The budgeted expression interfaces still need the numeric induction that constructs them. The first gate rejects before arguments with `Failure.stage`; second-gate arity rejects after arguments with `Failure.semantic`. A stage fault cannot be projected to an ordinary Dynamic fault. Both directions retain independently measured Source and Core grades and the same actual reached state.

Staged builtin application, terminal statements, receiving diagnostic adapters, the whole argument-prefix draft and later body drafts remain outside this package. Complete staged body recursion, call classification, scoped diagnostic composition, static compiler coverage, remaining recursive Source forms and the final all-pass public theorem are unfinished. Estimates remain 100% / about 70% / about 85%.

## Staged call diagnostics and terminal body interfaces (`1507404b`; 2026-10-11)

The twelve Sources below are registered through CoreLowering at `1507404b`. Normal validation checked all 184 owned declarations and 66 selected interfaces with literal private/normal TYPE/AXIOMS and complete API agreement. Build 5774 passed and the cumulative census grew from 19250 to 19434. Each Source had two independent nonauthor reviews. Module suffixes are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. These proof interfaces retain the existing public execution definitions.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `ReceivingPreparedShapeInterpretations` | `decoded_token_below`, `receiver_lookup`, `reached_interpretation` (3) | Actual accepted preparation bounds decoded tokens and preserves earlier receiving lookups through the sealed callable allocation; authentic receiver identity remains required. |
| `PreparedReceivingCallRejectionDiagnostics` | `reason_at_lower_bound`, `receiver_lookup`, `original_diagnostic`, `receiving_diagnostic` (4) | Same original selected call row and Site.reasonAt reach the actual receiving completion table; original metadata and selected issuer remain attached. |
| `PublicDecodedCallFaults` | `ErrorView`, `faults`, `stagedSemanticFaults`, `of_decoded`, `of_assignment`, `of_arity`, `of_staged_arity`, `arity_result`, `staged_arity_result` (9) | Concrete assignment and semantic arity views use the literal diagnostic table and physical counts; generic result forwarding retains the existing value model. |
| `PreparedReceivingCallRejectionPosts` | `selected_row`, `receiving_argument_post`, `receiving_staged_argument_post`, `row_at_source_view` (4) | Original BoundaryAt selects the row while CallView retains substituted metadata; physical mismatch yields a post at the actual argument heap/store and caller relation. |
| `PreparedReceivingFirstCallGateRejection` | `StageErrorView`, `stagedFaults`, `original_diagnostic`, `receiving_diagnostic`, `receiving_staged_post` (5) | StageErrorView keeps the actual invocation, failing scope, guard frame, SourceView, original Selected and GuardRejects; stage rejection keeps the actual callee post. |
| `AdmittedStagedTerminalStatements` | `Head`, `control`, `Head.trace`, `ResultRepresents`, `preserves`, `reflects` (6) | Four terminal value/fault rules are constructed from the actual Head and strict staged child hypotheses; return/tail controls retain exact tags and reached state. |
| `AdmittedStagedTerminalBody` | `code`, `code_rename`, `terminal_evaluates`, `flow_prefix`, `body_result`, `preserves`, `reflects` (7) | Actual terminal and footer binds produce original BodyResult for code.rename; strict child hypotheses retain independent grades, effects and reached admission. |
| `PreparedTerminalBodyCompilerReceipts` | `Terminal`, `Receipt`, `of_accepted`, `Receipt.head`, `Receipt.native_child`, `certificate` (6) | Accepted returnSome or singleton tail supplies the actual child action, predecessor fuel, result type and emitted footer; authentic child certificate remains explicit. |
| `PreparedTerminalStatementOrigins` | `substituted_contains`, `substituted_returning_iff`, `substituted_tail_iff`, `returning_origin`, `tail_origin`, `returning_head`, `tail_head` (7) | Forward SourceView transport recovers the original statement occurrence and form under substitution; node type equality remains separate. |
| `PreparedStagedTerminalBodyMeaning` | `fallback`, `source_head`, `emitted`, `preserves`, `reflects` (5) | Same accepted terminal receipt and SourceView construct Head and the actual emitted code.rename meaning using strict child E; original Source typing and compiler certificate remain cuts. |
| `PreparedStagedBuiltinApplicationBounds` | `source_value`, `preserves`, `reflects`, `argument_post` (4) | Represented ordered scalar arguments exclude builtin arity/type failures; original primitive P/R preserves the same argument state and independently grades the Source rule. |
| `PreparedStagedIndirectArgumentPrefix` | `source_rows`, `scoped_boundary`, `StageRejectedPrefix`, `ArgumentFaultPrefix`, `ApplicationPrefix`, `reflects_arguments` (6) | Actual parent inversion, original Source rows, scoped first gate and concrete ordered-argument reflection retain exact callee/argument posts and the strict application suffix. |

The first gate carries Failure.stage before arguments, with the exact failing scope and token. Physical arity mismatch at the second gate carries Failure.semantic after arguments. Both retain the concrete reached caller state and Source/Core effects. Numeric staged E hypotheses, authentic static certificate producers, whole application/body dispatch and complete Source/compiler coverage remain unfinished. Work estimates stay 100% / about 70% / about 85%.

Normal verification passed one registered build with 5774 jobs, twelve empty strict Source checks, and literal private/normal TYPE/AXIOMS agreement for all 184 complete owned declarations and complete API agreement for 66 selected interfaces, using only the standard three axioms. The cumulative census grew from 19250 to 19434 (+184), with no overlap or removals. The normal pre-install snapshot contained 5695 module rows; the current snapshot contains 5707. The independent BEFORE environment measured 2195 project modules and the compiled environment measured 2207. The existing CoreLowering object changed for registration; all fourteen modules in the reverse dependency cone were rebuilt, and all 4985 protected artifacts passed. All sixteen original normal receipts closed with exit code 0.

The independent BEFORE capture closed at `95d226` (`5e30b5`, session 27207); private full/API audit at `e7c58a` (`c4bffc`, session 59109); packet freeze at `ffc386` (`36c4ae`, session 8576); registered build at `335796` (`dc06e6`, session 62711); and normal validation at `8d3298` (`b29544`, session 57723). Code commit `1507404b20264fc300b656e9971205f3ecbf90a8` closed at `07591c`. The saved `staged-call-diagnostics-terminal-bodies-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `f3558384cf298fe7fd4d535eaafe4cd535435adef662b8e24db3b3cf80e013ba`. The checkpoint uses the original sixteen closed validation receipts; metadata finalization does not repeat their kernel runs.

## Staged call dispatch and terminal closure interfaces (2026-10-11; `6c165e33`)

`staged-call-dispatch-and-terminal-closures` is committed and normally verified at `6c165e33`. The twelve proof Sources contribute 106 complete module-owned declarations and 42 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19434 to 19540: 106 additions, no overlaps and no removals.

The registered build passes 5786 jobs. The independent selected dependency BEFORE contains 2250 modules; the compiled native environment contains 2262. The complete normal module snapshot changes from 5707 to 5719 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint uses these original sixteen closed receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `0799ac`; code commit `6c165e334b61a044e480e96ea9da7d414894817c` closed at `215010`. The saved `staged-call-dispatch-and-terminal-closures-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `dc631c0c098aee0e8a9fec163b3141d0142c3cb429aa78878f272d15a57c1ee3`. The corrected summary distinguishes the selected BEFORE environment of 2250 modules from the complete pre-install snapshot of 5707 module rows.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. All 42 interfaces below match the complete native and normal API logs. The 106 complete module-owned declarations also have literal private/normal TYPE/AXIOMS agreement.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `PublicDecodedStagedCallFaults` | `faults`, `of_semantic`, `of_first_gate`, `of_assignment`, `of_arity`, `decoded`, `semantic_result`, `first_gate_result`, `arity_result` | Literal receiving table keeps semantic and stage tags separate; exact call/scope/token result forwarding. |
| `PreparedStagedIndirectFirstGateBounds` | `result_at_rejected`, `preserves_rejected`, `reflects_rejected_prefix` | Strict callee preservation or authentic rejected-prefix reflection produces the same reached first-gate stage post. |
| `PreparedStagedIndirectSecondGateBounds` | `NamedOrigin`, `source_at_boundary`, `rejected_suffix`, `classify_application_prefix` | Original selected physical count produces semantic arity failure after arguments; authentic named provenance remains a static input. |
| `PreparedStagedIndirectArgumentFaultBounds` | `first_gate`, `preserves_argument_fault`, `reflects_argument_fault_prefix` | Strict callee and concrete ordered-argument fold produce the actual argument-fault post; prefix reflection retains that same fault. |
| `PreparedStagedIndirectApplicationSuffix` | `application_to_payload`, `application_from_payload`, `accepted_gate`, `reflects_suffix`, `preserves_suffix` | Literal payload normalization and accepted second gate retain the argument store and strict native application child. |
| `PreparedSelectedTerminalLambdaCompilerReceipts` | `of_receipt` | Retained NativeLambda recipe/body compilation constructs an accepted terminal compiler receipt before execution. |
| `PreparedStagedTerminalSourceBodyInversion` | `child_of_body`, `result_of_control` | Actual whole supported Source body yields the used child, strict Source grade and exact BodyResult/control. |
| `PreparedStagedBodyRestorationAdmission` | `restore_post` | Saved physical caller restoration transports the actual body admission for value, semantic fault or stage fault. |
| `PreparedStagedTerminalBodyTraceBounds` | `preserves_body` | Whole supported Source body supplies its child internally; strict expression preservation proves the emitted code.rename and full post. |
| `PreparedStagedClosureInvocationPostBounds` | `SourceBodyAt`, `ResultAt`, `invocation_preserves`, `NativeBodyAt`, `invocation_reflects`, `application_preserves`, `application_reflects` | Actual parameter/body prefixes and strict body hypotheses restore full caller admission; Source/Core grades remain independent. |
| `PreparedStagedIndirectFaultDispatch` | `FaultResult`, `reflects_fault_or_application` | Actual native parent returns callee/first-gate/argument fault meaning or preserves the right application prefix. |
| `PreparedStagedBuiltinArgumentRows` | `builtin_member`, `Rows`, `at_arguments`, `at_callee_post` | Authentic BuiltinAt/equal count plus original callee typing recover literal signatures and ordered scalar values at the argument post. |

The fault relation retains the actual receiving table and same result model/map/world. Stage rejection stays at the callee post; argument failure and second-gate arity stay at the reached argument post. PostAdmission carries deep Source admission for successful values and stable rows for faults. Complete body hypotheses and Scope/source provenance are not manufactured by decoding a diagnostic token.

Retained-callee argument prefixes (258), builtin whole-parent reflection/preservation (134/154), terminal body typing (96), metadata-body bounds (131), parameter-admission and concrete body-join drafts, and retained-callee fault/builtin dispatch drafts (127/216) are outside this twelve-Source checkpoint.

The numeric staged expression/argument/application/body induction, authentic static factories for complete compiler alternatives, general call/body dispatch and remaining recursive Source grammar remain unfinished. Specialization, evidence and comptime composition, general failure/export-error correspondence and the final public all-pass theorem are open. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall; declaration counts do not measure semantic completion.

## Staged parent and terminal lambda interfaces (2026-10-11; normally verified at `6844f7b0`)

`staged-parent-and-terminal-lambda-producers` is committed and normally verified at `6844f7b0`. The twelve proof Sources contribute 74 complete module-owned declarations and 26 selected interfaces. All twelve strict Source logs are empty, and complete private/normal TYPE/AXIOMS blocks and API logs agree literally. The cumulative census grows from 19540 to 19614: 74 additions, no overlaps and no removals. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews.

The registered build passes 5798 jobs. The independent selected dependency BEFORE contains 2218 modules; the compiled native environment contains 2230. The complete normal module snapshot changes from 5719 to 5731 rows. Twelve new regular Source/olean/ilean triples are installed. The only changed existing object pair is `CoreLowering`, within the fourteen-module dependency cone and fourteen actual rebuilds. All 4985 protected artifacts remain unchanged. Sixteen original normal validation receipts are closed with exit code zero. The checkpoint will use those original sixteen receipts; metadata finalization does not repeat their kernel runs.

Normal validation closed at `cc2cfe`; code commit `6844f7b0f788069d858f42a29343c7c5900829ba` closed at `5cea3d`. The saved `staged-parent-and-terminal-lambda-producers-checks.json` in `/private/tmp/solcore-owned-functions-resume-20261007` has SHA-256 `bf9f5a5635e9876005265366485f4f31bad0d297b3478785aa453b778561c456`. The selected BEFORE environment of 2218 modules is separate from the complete pre-install snapshot of 5719 module rows.

The strict child hypotheses are induction assumptions for the actual executed child: its Source trace grade is smaller for preservation, or its native evaluation grade is smaller for reflection. The shared numeric induction must still construct these hypotheses; the static compiler receipts do not contain a completed execution law.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. All 26 selected interfaces match the complete native and normal API logs. The 74 complete module-owned declarations also have literal private/normal TYPE/AXIOMS agreement.

| Module suffix | Selected interfaces | Semantic boundary |
| --- | --- | --- |
| `PreparedStagedIndirectRetainedCalleeArgumentPrefix` | `ApplicationPrefix`, `ApplicationPrefix.to_original`, `reflects_arguments` | Retains callee PostAdmission and raw typing through the actual argument fold; projects to the original application prefix. |
| `PreparedStagedBuiltinParentBounds` | `reflects_suffix` | Accepted builtin suffix constructs the original whole Source parent and full reached caller post. |
| `PreparedStagedBuiltinParentPreservation` | `preserves_parent` | The actual primitive and original binds construct the whole native builtin parent and caller post. |
| `PreparedStagedTerminalBodyTyping` | `child_typed`, `at_parameters` | Original body typing selects the genuine terminal child and declared result at parameter entry. |
| `PreparedStagedTerminalMetadataBodyBounds` | `source_head`, `preserves_body`, `reflects_body` | Actual metadata identifies the Source head; terminal body preservation/reflection retain the real used child and full post. |
| `PreparedLambdaParameterAdmission` | `install_rows`, `after_parameters`, `at_parameters` | Real parameter allocation and row histories construct entry admission without a supplied support law. |
| `PreparedStagedIndirectRetainedCalleeFaultDispatch` | `reflects_fault_or_application` | Whole-parent reflection returns the exact fault post or application prefix with retained callee typing. |
| `PreparedStagedIndirectBuiltinApplicationDispatch` | `UserApplicationPrefix`, `UserApplicationPrefix.to_retained`, `ParentResult`, `reflects_builtin_or_user` | Reflection constructs the accepted builtin result or arity fault, preserving the real user application prefix. |
| `PreparedStagedIndirectValuesPrefix` | `ValuesPrefix`, `preserves_values` | Strict callee P and the concrete ordered fold retain represented values at the actual argument post. |
| `PreparedStagedSuccessfulArgumentTyping` | `values_at`, `closure_at` | Successful Source arguments produce raw ordered typing, heap extension and the actual closure frame. |
| `PreparedStagedTerminalLambdaBodyBounds` | `source_body_at`, `native_body_at` | Code/registry derive child scope and parameter entry facts internally before strict terminal body preservation/reflection. |
| `PreparedStagedTerminalLambdaApplicationBounds` | `application_preserves`, `application_reflects` | Constructs the terminal body port at actual entry, then uses original closure application and caller restore once. |

The dependent caller post, callee typing, ordered argument heap and restored pool refer to the same actual execution. Builtin application has no function-body child. Terminal closure application still uses a strict expression hypothesis for its genuine compiled child. Physical gates retain their actual codebook count and rejected tag; Source and native grades are independent.

The shared numeric induction for expressions and function bodies, general user and named application dispatch, full statement grammar and authentic compiler occurrence coverage remain open. Specialization, evidence and comptime composition, general failures/export errors and the final public all-pass theorem are unfinished. Finite proofs for literals and grouping, the separate closure argument-typing producer and the whole builtin preservation dispatcher are outside this checkpoint. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.

## Staged call parent dispatch interfaces (2026-10-11; normally verified at `910e3e1d`)

`staged-call-parent-dispatch-bounds` is committed and normally verified at `910e3e1d`. Its seven proof Sources have 117 complete module-owned declarations and 19 selected interfaces. Every native and normal strict Source log is empty. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete 19-interface API logs are byte-identical. Each Source has its preserved isolated author pass and two genuine nonauthor Source reviews; the tooling has independent Root and Entry reviews.

The cumulative census is 19730 from 19614: 116 additions, one prior overlap and no removals. The overlapping generated helper, `ContextualCellOrigins.functions.congr_simp`, is literally unchanged. Build 5805 passes. The selected dependency BEFORE contains 2228 modules and the compiled native environment 2235; the complete normal snapshot changes from 5731 to 5738 rows. Seven new Source/olean/ilean triples are installed. Only the existing `CoreLowering` object pair changes, within the nine-module dependency cone and nine actual rebuilds. All 4985 protected artifacts remain unchanged.

The eleven original normal validation receipts are closed with exit code zero. Normal validation closed at `ce446f`; code commit `910e3e1d9f18c1fde867b7d56ef3321b5a0dd943` closed at `83f21b`. The saved `staged-call-parent-dispatch-bounds-checks.json` has SHA-256 `9360372c1f3e5abb9ab873e023f542f20bcfd58b301b46851ee5d9e7a108df4c`. Metadata finalization reuses the original eleven closed validation receipts without repeating their kernel checks.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. These are exactly the 19 selected interfaces of this seven-Source unit.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedClosureArgumentRows` | `source_arity`, `at_arguments` | Derives original physical Source arity and contextual closure argument/binder rows at the actual argument post. |
| `PreparedStagedTerminalClosureParentBounds` | `Terminal`, `TerminalFor`, `ReflectsBelowFor`, `application_reflects`, `reflects_suffix` | Reflects the selected terminal closure application and suffix, retaining the actual body result and full caller post. |
| `PreparedStagedTerminalClosureUserDispatch` | `GlobalApplicationPrefix`, `reflects_closure_or_global` | Reflects a closure, including its receiving arity fault, or retains the literal global application prefix. |
| `PreparedStagedTerminalClosureParentPreservation` | `PreservesBelowFor`, `application_preserves`, `preserves_parent` | Preserves the actual Source-selected terminal body/application and restores the saved caller once. |
| `PreparedStagedIndirectBuiltinPreservationDispatch` | `ParentAt`, `preserves_builtin_or_user` | Constructs the builtin parent or retains the actual user prefix, with physical mismatch handled at the real argument state. |
| `PreparedStagedIndirectSourcePrefixDispatch` | `NativeResultAt`, `ApplicationAt`, `preserves_fault_or_application` | Constructs real Source prefix failure parents or the successful application packet from actual strict children. |
| `PreparedStagedTerminalClosureUserPreservationDispatch` | `GlobalAppliedPrefix`, `preserves_closure_or_global` | Preserves the closure branch or retains the literal global applied prefix, including its Source parent grade and actual argument post. |

The strict child hypotheses describe the actual executed child: preservation uses a smaller Source trace grade, and reflection uses a smaller native evaluation grade. The shared numeric induction must still construct these hypotheses. Source and native grades are independent, and static compiler receipts retain authority rather than a completed execution law.

Completed parent results retain the full caller post for the same callee/argument execution. A retained global application prefix keeps reached Admission before its whole application is composed. Actual physical count and receiving row identify arity failures; tokens alone do not identify Source scope. Stage and semantic result interpretations remain separate.

The whole indirect parent reflection and preservation dispatch proofs, and terminal named invocation reflection, have saved author passes and genuine peer reviews in W. They are outside the seven registration targets, and their normal integration remains open. The whole parent proofs retain the actual named/global application prefix for further composition. Named invocation constructs the real parameter receipt, reflects the supported terminal body at its selected scope, and restores the caller; joining original raw global arguments, named physical arity, the outer indirect parent and the preservation direction remain separate obligations.

The shared numeric expression/function-body induction, general named application, full statement grammar and authentic compiler occurrence coverage remain open. Specialization, evidence and comptime composition, general failures/export errors and the final public theorem across all passes are unfinished. Finite literal, group and product-tree proofs remain a separate reviewed W unit. Estimates remain 100% for the first objective, about 70% for the second and about 85% overall.


## Finite staged expression and named call interfaces (2026-10-11; normally verified in two code commits)

`staged-finite-expressions-and-named-call-parents` is committed and normally verified in two logical code groups. The finite expression commit `5a5bdeffec4008cb4d6e972224b90b8a2df048db` contains four proof Sources, 102 module-owned declarations and 32 selected interfaces. The whole-call and named-call commit `ef75b2c3b86a2e2bc140ea274ae9ff55d86c99d2` contains seven Sources, 89 declarations and 18 interfaces. Together they add eleven Sources with 191 complete owned declarations and 50 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native strict logs and all eleven normal strict logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 191 declarations. The complete 50-interface API logs are byte-identical: 112327 bytes, SHA-256 `df758c72f09c97d7e7f17fee86fd94d67595c6adf117e6103b2bd158aa7f4058`. The independent selected BEFORE contains 2240 modules and the compiled native environment 2251.

The cumulative census grows from 19730 to 19921: 191 additions, no prior overlaps and no removals. Build 5816 passes. The complete normal snapshot grows from 5738 to 5749 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The original package tooling has independent Root and Entry reviews. The separate snapshot-copy successor was authored by Root and independently reviewed by Entry and Formal. Both code commits closed with exit code zero at actual receipt `0cb4aa`; normal validation records fifteen original CLOSED0 receipts. Its complete checks have SHA-256 `d48582c7b3291b9093a30b010b37f4805312f1b812e93c272b08ec96ed21d8cc`. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. The table lists exactly the 50 selected interfaces of this normally verified eleven-Source unit.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedGroupBounds` | `Group`, `Group.actual`, `of_literal_sites`, `group_preserves`, `group_reflects` | Retains the actual group child; Source preservation is strict, while native reflection recurses structurally at the same grade. |
| `PreparedStagedLiteralGroupBounds` | `Tree`, `Tree.literal`, `Tree.group`, `Tree.literal_sites`, `Tree.of_functions_literal`, `literal_preserves`, `literal_reflects`, `preserves`, `reflects` | Constructs the finite literal/group fold from actual literal receipts and grouped children. |
| `PreparedStagedPairBounds` | `Pair`, `Pair.actual`, `ProductValues`, `pair_preserves`, `pair_reflects` | Constructs ordered pair meaning at the actual intermediate state using strict evaluated bind children. |
| `PreparedStagedProductTreeBounds` | `Syntax`, `Syntax.literal`, `Syntax.group`, `Syntax.pair`, `Syntax.to_canonical`, `Tree`, `Tree.literal`, `Tree.group`, `Tree.pair`, `Tree.of_literal_sites`, `Tree.of_functions`, `preserves`, `reflects` | Extracts the supported finite syntax from actual LiteralSites and constructs the literal/group/pair fold. |
| `PreparedStagedIndirectTerminalReflectionDispatch` | `reflects_parent_or_global` | Reflects completed failure, builtin and terminal closure parents, or retains the literal global prefix. |
| `PreparedStagedIndirectTerminalPreservationDispatch` | `GlobalAt`, `preserves_parent_or_global` | Preserves completed failure, builtin and terminal closure parents, or retains the literal global applied prefix. |
| `PreparedStagedNamedPayloadReceipts` | `global_representation`, `named_payload` | Retains positive named payload authority, original source identity and dictionary. |
| `PreparedStagedNamedSourceScopeReceipts` | `global_view`, `record`, `selected`, `applies`, `arity_failure` | Derives the original Header record, selected row, staged Source scope and Source arity failure. |
| `PreparedStagedTerminalNamedBodyBounds` | `compiler_receipt`, `preserves_body`, `reflects_body` | Constructs the actual terminal compiler receipt and body preservation/reflection from strict child hypotheses. |
| `PreparedStagedNamedEntryBounds` | `Prefix`, `native_prefix` | Recovers the real named parameter/body prefix at the same reached pool and dictionary. |
| `PreparedStagedTerminalNamedInvocationBounds` | `parameter_receipt`, `ResultAt`, `reflects_invocation` | Constructs parameter authority and reflects the supported named invocation with exact saved-caller restoration. |

The finite expression fold constructs preservation and reflection for literals, transparent grouping and ordered two-element products from the actual compiler Tree and LiteralSites receipts. It retains original Source typing, the represented result, both staged and semantic failure interpretations, and the reached heap, store and caller post. Preservation descends on the independent Source trace grade. Reflection descends structurally through a transparent group at the same native evaluation grade; only children of actual evaluated pair binds require a strictly smaller native grade. The finite fold constructs its child meanings internally.

The whole indirect parent dispatch composes real callee, first-gate, ordered argument and physical-arity failure branches with accepted builtin and supported terminal closure application. Completed cases keep the exact restored caller PostAdmission at the returned pool. The named/global alternative retains the literal application prefix and reached Admission for an independent named consumer. First-gate stage failure and after-arguments semantic arity failure retain their distinct Source rules, tags and scopes.

The five named-call proofs retain the positive payload, original Header, selected record, Source scope, dictionary and actual parameter/body state. Supported terminal body preservation and reflection use the genuine compiled child with a separate strict child hypothesis. Invocation reflection constructs the parameter receipt, reflects the supported body once, and restores the saved caller in the actual returned pool. Its complete caller post refers to that same execution.

The shared numeric expression/function-body induction still has to provide strict hypotheses for the actual executed children; Source and native grades remain independent. Joining the original raw global argument list to the Header, connecting the independent named physical-arity receipt, composing the outer indirect parent and proving named invocation preservation remain open. General bodies, the full expression/statement grammar and authentic compiler occurrence and receiving-diagnostic coverage are unfinished. Specialization, evidence and comptime composition, general failures/export errors and the final public theorem across all passes remain open.

The separate real-cell read proof and finite compiler-factory proof remain reviewed work in the private proof area, outside these eleven registration targets. The first objective remains 100%; the second stays about 70%, and the equally weighted overall estimate stays about 85%. These estimates describe completed work, not declaration counts or remaining time.

## Finite read and named body interfaces (2026-10-11; normally verified in two code commits)

`staged-finite-reads-and-named-body-composition` is committed and normally verified in two logical code groups. The finite read/body commit `6d4fcbd855b387845dba4ca511ea66d6dde0c020` contains six proof Sources, 64 module-owned declarations and fourteen selected interfaces. The closure/named commit `ed30cd3be8a2f9b11e5ff21387a19f8fcfdbde99` contains five Sources, 56 declarations and twenty-two interfaces. Together they add eleven Sources with 120 complete owned declarations and 36 selected interfaces. Each Source retains its isolated author pass and two genuine nonauthor Source reviews.

All eleven native and eleven normal strict Source logs are empty. Complete private/normal TYPE/AXIOMS blocks agree literally for all 120 declarations. The complete 36-interface API logs are byte-identical: 108225 bytes, SHA-256 `79a0c159998685d6e97f3c1c1302f389d6ffcba81df469023faf1e62582b2e2c`. The independent selected BEFORE contains 2274 modules and the compiled native environment 2285.

The cumulative census grows from 19921 to 20041: 120 additions, no prior overlaps and no removals. Build 5827 passes. The complete normal snapshot grows from 5749 to 5760 rows, with eleven new regular Source/olean/ilean triples. Only the existing `CoreLowering` object pair changes. The dependency cone and actual rebuild set each contain thirteen modules; all 4985 protected artifacts remain unchanged.

The selected tooling has independent Root and Entry reviews; the inherited snapshot-copy change retains its genuine Entry and Formal reviews. Both code commits and all fifteen original normal validation receipts are closed with exit code zero. The complete checks have SHA-256 `ce9c5751d088be73b668e9f76a8f64ce7f2c126d873dc8ae03102f7ccf498ed6`. Metadata finalization reuses the original fifteen closed normal validation receipts without repeating their kernel checks.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. This table lists the exact 36 selected interfaces, not a native declaration census.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedReadBounds` | `preserves`, `reflects` | Proves actual real-cell read preservation/reflection, including authentic uninitialized reads and lazy mapping writes. |
| `PreparedStagedNamedReadDiagnostics` | `decoded_read`, `uninitialized`, `staged_uninitialized` | Produces the certified read diagnostic and uninitialized interpretation in the recursively staged semantics from the same issuer and receiver. |
| `PreparedStagedContextualProductReceipts` | `of_contextual` | Extracts an actual contextual Tree.WithLiterals using the genuine literal producer. |
| `PreparedStagedNamedTerminalChildReceipts` | `source_child`, `finite_child` | Derives the original typed terminal child and its finite compiler certificate from the Header. |
| `PreparedStagedReadProductTreeBounds` | `Certificate`, `of_functions`, `preserves`, `reflects` | Constructs the accepted read/literal/group/pair fold with internally discharged child meaning. |
| `PreparedStagedFiniteNamedBodyBounds` | `preserves_body`, `reflects_body` | Constructs finite named body preservation/reflection without an external child expression law. |
| `PreparedTerminalClosureFactories` | `of_actual_body_exact`, `of_actual_body`, `TerminalShapeFor`, `ReadPolicyFor`, `HasBodyCertificate`, `HasBodyChild`, `terminal_for_exact`, `terminal_for`, `at_prepared_registry`, `at_prepared_registry_exact` | Retains authentic terminal shape, read policy and the exact accepted body child at the selected scope. |
| `PreparedTerminalClosureFactoryBounds` | `ReflectsActualBodyBelow`, `PreservesActualBodyBelow`, `application_reflects`, `application_preserves` | Consumes actual selected-child semantic hypotheses to construct complete closure application results. |
| `PreparedStagedTerminalNamedInvocationPreservation` | `body_prefix`, `preserves_invocation` | Inverts the actual Source body prefix and constructs named invocation preservation with saved-caller restoration. |
| `PreparedStagedNamedArgumentRows` | `caller_supports`, `accepted_rows`, `at_successful_arguments` | Derives caller support and typed ordered rows at the original selected node/metadata and actual argument post. |
| `PreparedStagedTerminalNamedApplicationBounds` | `carrier`, `application_preserves`, `application_reflects` | Constructs the literal named carrier and both application directions using the generic invocation producers. |

Named read diagnostics come from the actual prepared Header, diagnostic receipt and receiving issuer. The uninitialized-read interpretation is indexed by the certified read occurrence, including its binder, span and reason token; decoding does not manufacture a Source fault. The Header and accepted terminal receipt supply the real child typing and finite compiler tree. The finite named body producer calls this fold directly in both directions, removing its external child-expression meaning and arbitrary certificate callback. It keeps the actual parameter entry and selected body scope, and carries the returned heap, store, map, world, relation and PostAdmission.

The closure factories retain an exact accepted body child and its authentic static support. Their application consumers still require meaning for the actual selected child. Named invocation preservation constructs the real parameter allocation, uses the selected terminal body, and restores the caller at the returned pool. Named argument rows retain the original selected node and metadata, the Source argument types and the independent physical-count receipt. The literal named carrier supports both application directions at those exact endpoints. These generic invocation/application proofs still consume strict child hypotheses; they do not yet instantiate the new finite body producer.

The next finite named invocation/application proof will retain the substantive parameter-entry and restoration proofs and replace their body call with the finite named body producer. It must preserve the actual Source-selected child in preservation and the authenticated Header/descriptor scope in reflection, with real ledger, runtime, coverage, ordinary-metadata and finite-syntax premises. The shared numeric expression/function-body family, outer named/global joins, full compiler and Source grammar, general bodies and complete receiving-diagnostic coverage remain open. Specialization, evidence and comptime composition, general failure/export-error correspondence and the public theorem across all passes are unfinished. Estimates remain 100% for runtime unification, about 70% for the second objective and about 85% overall.

## Finite call body and global join interfaces (2026-10-11; normal verification complete)

The selected `staged-finite-call-bodies-and-global-joins` work contains nine proof Sources and 37 selected interfaces. The three generic parent/global joins expose seven interfaces; the two static closure-child producers expose twelve; the four finite call/body proofs expose eighteen. Each selected Source has an isolated author pass and two genuine nonauthor Source reviews. Normal verification passes for all nine Sources, 177 module-owned declarations and 37 selected interfaces. The generic joins contribute 68 declarations, the static closure-child producers 27, and the finite call/body proofs 82. The three code commits are `c37620a6`, `b568df64` and `ef72f57e`.

| Validation item | Completed result |
| --- | --- |
| Selected proof scope | Nine Sources / 37 interfaces, with isolated author passes and two genuine nonauthor Source reviews each. |
| Native and normal strict checks; full literal TYPE/AXIOMS/API audits | All nine strict Source logs are empty. All 177 complete module-owned TYPE/AXIOMS blocks agree literally; the 37-interface API logs are byte-identical (195517 bytes, SHA-256 `a601df8af4153992798319bc93f9f0d4870323bf5cebf5f4a30114070d61d9ec`). |
| Independent selected BEFORE and compiled environment | 2312 modules before the selection; 2321 in the actual compiled environment. |
| Registered build and normal snapshot | Build 5836 passes; the full normal snapshot grows from 5760 to 5769 rows. All thirteen original normal validation receipts close with exit code zero. |
| Cumulative additions, overlaps, removals and current census | 20041 → 20218: 177 additions, no prior overlap and no removals. |
| Existing object changes, dependency cone, rebuilds and protected artifacts | Only the existing `CoreLowering` object changes. The reverse dependency cone and actual rebuild each contain eleven modules; all 4985 protected artifacts remain unchanged. |
| Code commits | Generic named joins: `c37620a6` (three Sources / seven interfaces / 68 declarations); static closure children: `b568df64` (two / twelve / 27); finite call bodies: `ef72f57e` (four / eighteen / 82). |

Metadata finalization reuses the original thirteen closed validation receipts without repeating their kernel checks.

Preservation constructs native execution from an actual Source derivation. Reflection reconstructs a Source derivation from native completion with an independent Source grade. Both retain the actual reached heap, store, map, world, relation and returned pool. Completed application and parent results retain full caller PostAdmission, including the original tag and scope of nested stage failures.

Module suffixes below are under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwned`. The table lists the exact 37 selected interfaces; it is not a native declaration census.

| Module suffix | Selected interfaces | Concrete boundary |
| --- | --- | --- |
| `PreparedStagedTerminalNamedParentBounds` | `preserves_parent`, `reflects_suffix` | Constructs the generic named parent or reflects its accepted suffix at the authentic ordered argument post; strict child hypotheses remain explicit. |
| `PreparedStagedTerminalNamedGlobalDispatch` | `Terminal`, `reflects_global`, `preserves_global` | Runs the generic named parent at the selected equal count, or retains the actual Source arity failure and receiving diagnostic. |
| `PreparedStagedIndirectTerminalCallBounds` | `reflects_parent`, `preserves_parent` | Connects the actual whole indirect completion or Source trace to generic closure, builtin and named-global branches; child hypotheses remain explicit. |
| `PreparedTerminalClosureCanonicalChildFactories` | `canonical_child`, `HasCanonicalBodyChild`, `canonical_for`, `terminal_for_both`, `at_prepared_registry_both` | Retains the exact original-Source child and corresponding compiler child from the same accepted BodyWith without metadata typing assumptions. |
| `PreparedTerminalClosureUsedChildBounds` | `Point`, `narrow`, `narrowFor`, `ReflectsUsedChildBelow`, `PreservesUsedChildBelow`, `application_reflects`, `application_preserves` | Narrows the certificate to the actual used child and supplies both application directions from strict selected-child hypotheses. |
| `PreparedStagedFiniteNamedInvocationBounds` | `carrier`, `preserves_invocation`, `reflects_invocation`, `application_preserves`, `application_reflects` | Constructs finite named invocation/application directly from the finite body at the real parameter entry and restores the saved caller. |
| `PreparedStagedFiniteNamedParentBounds` | `preserves_parent`, `reflects_suffix` | Constructs the finite named parent and reflects its accepted suffix from authentic Source/native argument rows and the finite application. |
| `PreparedStagedFiniteNamedGlobalDispatch` | `Terminal`, `reflects_global`, `preserves_global` | Recovers the actual positive Header and constructs finite global dispatch, including its receiving semantic arity fault. |
| `PreparedStagedFiniteClosureBodyBounds` | `Family`, `FiniteBody`, `canonical_child`, `raw_child`, `child_preserves`, `child_reflects`, `application_preserves`, `application_reflects` | Extracts the canonical typed child from a fixed finite BodyWith and constructs finite closure child/application meaning internally. |

Finite named invocation and application now call the finite named body producer directly at the actual parameter entry. Preservation retains every actual Source-selected body scope; reflection retains the authenticated Header/descriptor-selected scope. The proof runs the original parameter installation and body prefix once, uses the finite read/literal/group/pair body once, and restores the saved caller at the actual returned pool. It no longer takes an external child-expression meaning hypothesis or arbitrary certificate callback.

The finite named parent derives typed Source arguments and represented native parameters from the authentic ordered rows and independent physical-count receipt. Its accepted suffix uses that same finite application once. The finite global dispatcher recovers the real Header, dictionary, capture and Source frame from the positive named payload. It either runs the finite parent at the selected equal count or proves the actual Source semantic arity failure with the exact receiving diagnostic at the reached argument post. First-gate `Failure.stage` and second-gate semantic arity failure remain separate.

The finite closure body proof retains a fixed accepted BodyWith with both compiler-view and original-Source trees. Authentic frame typing and the selected Source scope provide the raw child type; the exact original child certificate feeds the finite evaluator. Its application proofs construct read/literal/group/pair child meaning internally and retain the restored caller post. Genuine finite-family compiler transport, terminal/read policy, certified read-fault interpretation, registry extension and runtime premises remain explicit.

The generic named parent/global joins and whole terminal indirect-call proof connect actual callee and ordered-argument prefixes to the original payload application and native suffix. They keep transient effects and the complete restored caller post. These generic ports still require authentic terminal factories and strict child induction hypotheses: those hypotheses assert child execution only below the enclosing numeric budget.

The static closure-child producers retain the exact accepted child in both original and compiler Sources, then restrict a requested child certificate to that literal occurrence. They do not infer raw typing from a metadata view or turn an arbitrary static certificate family into finite semantics.

The shared numeric expression/function-body family and general callee/argument recursion remain open. The finite named and closure application proofs do not yet instantiate every generic whole-call child hypothesis. Constructing the fixed finite closure support from every actual compiler path still needs genuine reachable certificate transport. Wider expression/statement grammar, general bodies, complete receiving-diagnostic coverage, specialization/evidence/comptime composition and the final public theorem across all passes are unfinished. Runtime unification remains 100%; the second objective remains about 70%, with an equally weighted overall estimate of about 85%. These are estimates of completed work, not declaration counts or remaining time.

## Finite closure dispatch and arbitrary tuple proof interfaces (2026-10-11)

`staged-finite-call-dispatch-and-tuple-folds` is normally verified in three code commits: `fb42f8c2` adds the finite closure parent, static transport and terminal packet (three modules, thirteen interfaces); `280557de` adds the arbitrary tuple fold and compiler issuer (two modules, six interfaces); `a48286e4` connects the whole-call and user dispatch branches (six modules, eight interfaces). The eleven modules expose 27 selected interfaces and 156 owned declarations. Each Source has two genuine nonauthor Source reviews.

All eleven fresh private and normal strict Source checks closed with empty output. Complete TYPE/AXIOMS and API audits passed, and the private and normal API logs are byte-identical (142486 bytes). The native import closure grew from 2319 to 2330 modules. The registered build completed 5847 jobs; normal Source/BOTH rows grew from 5769 to 5780. The only changed existing object was `CoreLowering`; all eleven new modules have regular objects, all thirteen modules in the reverse dependency cone were rebuilt, and 4985 protected artifacts stayed unchanged. The cumulative census grew from 20218 to 20374, with 156 additions, no overlap and no removals. Metadata finalization reuses the original fifteen closed validation receipts without repeating their kernel checks.

| Module in `Solcore.SourceSemantics.CoreLowering` | Selected interfaces | Proof boundary |
| --- | --- | --- |
| `CallableIndexedOwnedPreparedStagedFiniteNamedIndirectCallBounds` | `reflects_parent`, `preserves_parent` | Connects the finite named branch to whole-call preservation/reflection; genuine caller and closure child hypotheses remain explicit. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureParentBounds` | `FiniteTerminal`, `FiniteFor`, `application_preserves`, `application_reflects`, `reflects_suffix`, `preserves_parent` | Constructs finite closure application and joins its literal suffix to the full restored caller post. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureStaticTransport` | `finite_syntax`, `literal_sites`, `certificate`, `syntax_original`, `certificate_original`, `of_tree` | Transports finite syntax and literal/read certificates at authentic reachable unedited occurrences, then constructs the same finite body. |
| `CallableIndexedOwnedPreparedStagedTupleTreeBounds` | `Certificate`, `preserves`, `reflects` | Constructs ordered arbitrary-tuple preservation/reflection internally, including same-grade singleton reflection. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureTerminalPackets` | `of_tree` | Constructs the exact finite terminal packet from the accepted body tree and selected Source scope. |
| `CallableIndexedOwnedPreparedStagedTupleCompilerReceipts` | `Syntax`, `PolicyFor`, `of_functions` | Extracts a positive tuple certificate from genuine accepted compiler actions and raw child typing. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureUserDispatch` | `reflects_closure_or_global` | Reflects a closure, including its receiving semantic arity fault, or retains the actual global application prefix. |
| `CallableIndexedOwnedPreparedStagedFiniteClosureUserPreservationDispatch` | `preserves_closure_or_global` | Preserves the actual closure application or retains the literal global Source suffix at the reached argument state. |
| `CallableIndexedOwnedPreparedStagedIndirectFiniteClosureReflectionDispatch` | `reflects_parent_or_global` | Reflects failure, builtin and finite closure parent branches; retains global dispatch and strict caller child hypotheses. |
| `CallableIndexedOwnedPreparedStagedIndirectFiniteClosurePreservationDispatch` | `preserves_parent_or_global` | Preserves failure, builtin and finite closure parent branches; retains global dispatch and strict caller child hypotheses. |
| `CallableIndexedOwnedPreparedStagedFiniteIndirectCallBounds` | `reflects_parent`, `preserves_parent` | Combines finite named and closure application; strict caller callee/argument hypotheses remain explicit. |

The arbitrary tuple fold supports nested finite tuples of any arity, including repeated child identifiers, in their original order. It internally constructs the read/literal/group/pair leaves and evaluates each next child at the actual intermediate caller state. Preservation uses the actual Source grades, including the legacy two-element pair rules. Reflection uses structural child descent when a singleton's native packer erases the tuple wrapper and keeps the same grade. The compiler issuer extracts this certificate from the actual accepted action and ordered child vector, with original raw typing and static policy inputs; no leaf execution law is supplied.

The next substantive cut is a recursive static caller certificate whose read/literal/group/tuple/call fold constructs those child hypotheses internally. The current tuple issuer admits groups only inside its older leaf grammar, not groups around a new arbitrary tuple or call. Finite closure transport and terminal bodies still use the narrower read/literal/group/binary-pair grammar. Authentic compiler policy, raw typing, selected Header or Association, registry/receiving diagnostics, runtime ledger and coverage remain inputs. Shared numeric expression/application/body induction, general recursive bodies, broader expression and statement grammar, and the final public all-pass theorem remain unfinished. Runtime unification stays 100%; the second objective stays about 70%, and the equally weighted overall estimate stays about 85%.

## Recursive caller certificates and compiler composition (2026-10-11)

The selected `staged-recursive-callers-and-static-receipts` unit is normally verified in `e8607d82` and `abe72325`: six proof Sources, 198 owned declarations and 37 selected interfaces. Each Source has an isolated strict author pass and two independent nonauthor Source reviews.

All six native and normal strict Source checks have empty logs. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete API logs are byte-identical (89589 bytes, SHA-256 `05cacd2519262ad3ad8a8762e6110fde41596f12f27aa90b3638ffdfdfe4eafb`). The selected native environment grows from 2324 to 2330 modules. Build 5853 passes; the normal Source/BOTH snapshot grows from 5780 to 5786 rows. The cumulative census grows from 20374 to 20572: 198 additions, no overlap and no removals. All 8 modules in the affected dependency cone are rebuilt and all 4985 protected artifacts remain unchanged.

Metadata finalization reuses the original ten closed validation receipts without repeating their kernel checks.

| Module suffix under `Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStaged` | Selected interfaces | Role |
| --- | --- | --- |
| `RecursiveCallerSourceReceipts` | 4 | Derives original call-node alignment, raw child typing and actual callable preparation. |
| `TupleHeadBounds` | 2 | Assembles ordered tuple preservation/reflection from the structural child hypotheses at the actual intermediate states. |
| `FiniteCallHeadBounds` | 4 | Retains the authentic call port and joins one finite whole-call result to expression preservation/reflection. |
| `RecursiveCallerCertificates` | 21 | Defines supported syntax, policy, recursive certificates and reachable call receipts, then issues the root from an accepted compiler action. |
| `RecursiveCallerBounds` | 4 | Builds caller child preservation/reflection internally by structural induction. |
| `RecursiveCallerCompilerBounds` | 2 | Connects the actual accepted compiler action and generated root to the preservation/reflection fold. |

The Source receipt APIs are `original_read_metadata`, `source_parent`, `original_child_types` and `prepared`. Tuple heads expose `tuple_preserves` and `tuple_reflects`; call heads expose `Point`, `Port`, `preserves` and `reflects`.

The certificate module exposes `Syntax`, `PolicyFor`, `Certificate`, `Calls` and `of_functions`, together with their sixteen selected constructors or fields. The fold exposes `Point`, `CallsReady`, `preserves` and `reflects`. The compiler wrapper exposes `preserves_compiled` and `reflects_compiled`; both construct the root certificate from the actual accepted compiler action.

The compiler issuer starts from the actual accepted lowering action and original Source typing. It recovers the original indirect-call node, raw callee type and ordered argument types before building the child certificate. The certificate retains groups, tuples and indirect calls recursively, including groups around new tuple or call nodes. Argument entries keep their original order and repeated identifiers.

Structural induction on that certificate proves both preservation and reflection at every actual reached state. Child execution hypotheses are constructed internally. Group reflection and erased singleton tuple packing can use the same native grade; induction follows the child certificate rather than assuming a smaller execution grade. An indirect call uses the actual callee entry and ordered argument tree, then the existing finite whole-call proof once. Results retain the reached heap, store, map and world, exact staged fault scope, returned pool, caller relation and PostAdmission. Source and native grades remain independent.

The compiler-facing wrapper constructs its root certificate internally. Its `CallsReady` premise refers only to call receipts reachable from that exact generated root. Actual preparation, Source view, sidecar, guard frame, selected Header or Association, receiver, registry extension, diagnostic interpretation, ledger and coverage remain static or runtime premises. Called bodies still use the existing finite read/literal/group/binary-pair family. No public child execution or arbitrary body meaning callback is supplied.

General recursive called bodies, the shared numeric expression/application/body family, other expression and statement forms, and specialization/evidence/comptime composition remain unfinished. The final public theorem across all compiler passes is incomplete. Estimates remain 100% for runtime unification, about 70% for meaning preservation and about 85% overall.

The static Source/compiler receipt group (`e8607d82`) contains two Sources, 125 declarations and 25 selected interfaces. The semantic head/fold/compiler composition group (`abe72325`) contains four Sources, 73 declarations and twelve interfaces. Interface and declaration counts do not measure proof completion.

## Selected caller and recursive terminal body interfaces (2026-10-11; normal verification complete)

The selected `staged-selected-callers-and-recursive-body-bounds` unit is normally verified in `7db7dd2c`, `dda78f9c`, `31549a17`: sixteen proof Sources, 376 owned declarations and 53 selected interfaces. Each Source has an isolated strict author pass and two independent nonauthor Source reviews, excluding contributing repair authors.

All sixteen native and normal strict Source checks have empty logs. Complete private/normal TYPE/AXIOMS blocks agree literally, and the complete API logs are byte-identical (215570 bytes, SHA-256 `40020d9c5a18129f8d398856d30533f3fbbb94a7d853a9d9bc783fc51eb820e9`). The selected native environment grows from 2317 to 2333 modules. Build 5869 passes; the normal Source/BOTH snapshot grows from 5786 to 5802 rows. The cumulative census grows from 20572 to 20948: 376 additions, no overlap and no removals. All 18 modules in the affected dependency cone are rebuilt and all 4985 protected artifacts remain unchanged.

Metadata finalization reuses the original twenty closed validation receipts without repeating their kernel checks.

| Module suffix under `CallableIndexedOwnedPreparedStaged` | Selected interfaces | Role |
| --- | --- | --- |
| `SelectedTerminalCertificates` | 4 | Narrows the certificate to the actual chosen terminal child. |
| `SelectedTerminalClosureParentBounds` | 1 | Reflects the selected closure application and original parent. |
| `SelectedTerminalClosureParentPreservation` | 1 | Preserves the selected closure application and original parent. |
| `SelectedTerminalNamedGlobalDispatch` | 2 | Connects the actual selected named Header and global application. |
| `SelectedTerminalClosureUserDispatch` | 1 | Reflects user arity and accepted selected closure dispatch. |
| `SelectedTerminalClosureUserPreservationDispatch` | 1 | Preserves user arity and accepted selected closure dispatch. |
| `SelectedIndirectTerminalReflectionDispatch` | 1 | Reflects actual callee and ordered argument prefixes. |
| `SelectedIndirectTerminalPreservationDispatch` | 1 | Preserves actual callee and ordered argument prefixes. |
| `SelectedIndirectTerminalCallBounds` | 2 | Joins selected closure and named whole-call branches. |
| `SelectedGeneralCallHeadBounds` | 4 | Connects one authentic whole-call result to expression meaning. |
| `SelectedRecursiveCallerBounds` | 4 | Builds caller child meaning by structural certificate induction. |
| `SelectedBodyStaticSupport` | 9 | Retains original Root/RootAt and named/Association static authority. |
| `SelectedRecursiveBodyBounds` | 10 | Constructs selected terminal body meaning by numeric induction. |
| `SelectedCallerFromRecursiveBodies` | 2 | Uses the constructed body family in the caller fold. |
| `SelectedBodyCompilerSupport` | 2 | Issues original Source roots from actual accepted compiler actions. |
| `RecursiveBodyViewTransport` | 8 | Transports accepted compiler-view lowering to the original Source. |

The call chain selects one authentic terminal packet for the actual named Header or contextual closure Association. Its certificate is narrowed to that packet's original expression, scope and lowered child. Closure and named dispatch retain the real argument order, physical arity, staged rejection and selected scope. The accepted application keeps its actual returned pool and restores the saved caller, including caller relation and PostAdmission.

The selected caller fold constructs callee and argument preservation/reflection internally from the actual recursive certificate. Group reflection and erased singleton tuple packing may keep the same native grade; their induction follows the child certificate. Ordered argument entries retain repeated identifiers and use the actual intermediate state. Numeric strong induction then constructs meaning for supported selected terminal bodies at strictly smaller semantic budgets. The caller-from-bodies adapter consumes that constructed body family. These endpoints require no external child execution or body meaning callback. Source and native grades remain independent.

Static body support retains the original Source root, raw context, actual Header or Association body context and every genuinely selected child scope. The compiler support issues a certificate from the actual accepted original action and indexes call readiness by that exact proof. The compiler-view transport proves accepted lowering on the original Source from paired policies, reached unedited metadata and the real compiler action. Compiler callbacks, reason functions, original typing/declarations, receiver, registry extension, diagnostics, runtime ledger and coverage remain explicit authority inputs.

This closes the supported selected terminal body/caller recursion. Constructing these authentic roots and authority packets for every compiler path remains unfinished. Wider expression and statement grammar, unrestricted function bodies, complete receiving-diagnostic coverage, specialization/evidence/comptime composition and the final public theorem across all passes are still open. Runtime unification remains 100%; meaning preservation remains about 70%, with an equally weighted overall estimate of about 85%. These estimates describe completed work, not interface counts or remaining time.
