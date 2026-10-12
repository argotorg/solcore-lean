import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation
import Solcore.Frontend.SourceCoreFailurePreservationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedHistoryPublicBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapGlobalReferences
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryArgumentsReceiving
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! Source success of a following named call produces sufficient public fuel
and a reusable history at the actual input registry. Current history provides
heap, arguments and captured functions; output follows from representation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association (headers rows) (keys compiled) bodyRegistry semanticFaults
      mapping world function native bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers rows → Body header)
  (namedSupport : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (keys compiled) bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {recipe : SourceCoreIndexedSession.Recipe}
  (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {anchor : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : State (headers rows) (keys compiled)
    ⟨[], mapping, world, before, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
  (history : RecursiveNamedPublicFunctionHistory.History (headers rows) (keys compiled)
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) completion.result.context.registry anchor
    nativeSession mapping world before store caller entries)
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {options : SourceCoreExecution.RunOptions}
  {publicArguments : List SourceCorePublicValues.Value} {arguments : List Dynamic.Value}
  {payloads : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  (inputReceipts : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries
    header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
    publicArguments arguments)
  (atRegistry : nativeSession.RegistryAt completion.result.context.registry)
  (exportsReady : nativeSession.ExportsReady)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope}

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver observations semantic family namedTerminals namedSupport wellFormed
  prepared selected history atCheckpoint started inputReceipts sourceAt atRegistry exportsReady in
/-- A following named call keeps all prior captures and ordered entries at its
actual returned session. Both fuel bounds follow from the independent Source
success; native completion and successful export are conclusions. -/
theorem public_resume_has_sufficient_fuel
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
      (.global function) arguments (.value sourceResult) after) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, nativeCheckpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
      (payload : Core.Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (requiredExecution requiredOutput : Nat),
      (∀ executionFuel, requiredExecution ≤ executionFuel →
        nativeCheckpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := receiving.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions rootOwner caller header capture anchor.function.context (.value sourceResult) after
        (.inRight .word payload) finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : SourceCoreIndexedSession.Completion nativeArtifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore),
          outcome = .succeeded publicCompletion ∧
          nativeCheckpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧ Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            receiving.result.context.registry anchor actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start history atRegistry started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.current_arguments
      (completion := receiving) (inputs := inputs) (rows := rows) (profile := profile)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (history := retained) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_root
      (stagePrepared := stagePrepared) (receiver := issued) (profile := profile)
      (observations := observations) (extension := receiving.result.extension) (semantic := semanticAt)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled)
      (wellFormed := wellFormed) (selected := selected) (owner := owner recipe.compiled)
      (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt)
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).2) trace
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      nativeCheckpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : ValueRep recipe.compiled.compatible.checked receiving.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile)
      finalMap finalWorld header.function.resultType sourceResult payload header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [contextAt] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : nativeCheckpoint.RegistryAt encodedValues.registry := by
    have values := started.values
    cases nativeCheckpoint
    change _ = encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  have checkpointReady := started.original.initial_registry.exportsReady exportsReady
  obtain ⟨requiredOutput, exports⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨receiving, contextAt, issued, extended, diagnostics, capture, payload,
    finalStore, finalMap, finalWorld, requiredExecution, requiredOutput, completes, result, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨publicCompletion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, related, retained⟩ :=
    retained.after_success rfl started selected exported result
  exact ⟨publicCompletion, actual, generation, reached, succeeded, exported, actualAt,
    related, retained, started.returned_registry exported, returnedReady⟩


include receiver observations semantic family namedTerminals namedSupport wellFormed
  prepared selected history atCheckpoint started inputReceipts sourceAt atRegistry exportsReady in
/-- Independent Source failure of the actual ordered named call fixes the
public token and reached heap for every sufficient execution budget. Output
fuel may be zero; the failed session retains earlier captures and export authority. -/
theorem public_resume_fault_has_sufficient_fuel
    {sourceSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation anchor.function.context before
      (.global function) arguments (.fault failure) after) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, nativeCheckpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header mapping world)
      (token : Word) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) failure token ∧
      (∀ executionFuel, required ≤ executionFuel →
        nativeCheckpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := receiving.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions rootOwner caller header capture anchor.function.context (.fault failure) after
        (.inLeft header.output (.word token)) finalStore finalMap finalWorld (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact)
          (actual : SourceCoreIndexedSession.Session nativeArtifact)
          (reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          nativeCheckpoint.FailedResultAt executionFuel (.inLeft header.output (.word token)) finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            receiving.result.context.registry anchor actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start history atRegistry started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨stable, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicBounds.current_arguments
      (completion := receiving) (inputs := inputs) (rows := rows) (profile := profile)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (history := retained) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  have globalReference := CallableIndexedOwnedPreparedBootstrapGlobalReferences.global_reference rows header selected.member
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_root
      (stagePrepared := stagePrepared) (receiver := issued) (profile := profile)
      (observations := observations) (extension := receiving.result.extension) (semantic := semanticAt)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled)
      (wellFormed := wellFormed) (selected := selected) (owner := owner recipe.compiled)
      (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt)
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).2) trace
  obtain ⟨token, valueEq, faultRelated⟩ : ∃ token,
      value = .inLeft header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token := by
    have representation := result.2.1
    cases representation with
    | fault related => exact ⟨_, rfl, related⟩
  subst value
  have completes : ∀ executionFuel, required ≤ executionFuel →
      nativeCheckpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore :=
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound)
  have supports := (RecursiveNamedPublicReturnedValues.header_context_supports header anchor wellFormed).1
  have callerHeap := heapTyped.transportContext supports
  have callerArguments := argumentsTyped.transportContext supports
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.FaultPreservation.applies wellFormed
    (RecursiveNamedPublicHistorySourceInputs.header_runtime wellFormed anchor) callerHeap
    (RecursiveNamedPublicHistorySourceInputs.source_typed wellFormed sourceAt anchor before)
    packing (packing.hasType callerArguments) trace
  have checkpointReady := started.original.initial_registry.exportsReady exportsReady
  refine ⟨receiving, contextAt, issued, extended, diagnostics,
    capture, token, finalStore, finalMap, finalWorld, required, faultRelated, completes, result, ?_⟩
  intro executionFuel outputFuel outcome bound resumed
  have completed := completes executionFuel bound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed rfl
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, continued⟩ :=
    retained.after_failure rfl started selected failed result preserved.1
  have returnedRegistry : actual.RegistryAt encodedValues.registry := by
    have values := failed.2.2.2.2.1.trans started.values
    cases nativeCheckpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  exact ⟨returned, actual, reached, outcomeEq, failed, returnedAt, related, continued, returnedRegistry, failed.exportsReady checkpointReady⟩


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
