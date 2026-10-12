import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! Independent successful Source execution of the first named factory
produces sufficient native fuel, genuine function export and the first reusable
History. Export authority is retained by the actual bootstrap operation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedFunctionPreservation
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
  (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
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
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
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
  {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
  {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
  {publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {bootstrapFuel : Nat} {options : SourceCoreExecution.RunOptions}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
  (fresh : publicBootstrap.FreshAt)
  (ready : publicBootstrap.ReadyAt bootstrapFuel publicSession)
  (authority : publicBootstrap.ExportAuthorityAt)
  (atSession : publicSession.IndexedAt nativeSession)
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  {arguments : List Dynamic.Value}
  (inputReceipts : RecursiveNamedPublicNestedInputs.Inputs rows nativeSession
    header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
    publicArguments arguments)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope}

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include distinct receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared selected opened fresh ready authority atSession atCheckpoint started inputReceipts metadata sourceAt in
/-- Native completion and output export are conclusions. The independent Source
trace supplies the result and heap; every sufficiently fueled real resume keeps
that exact result in a singleton retained collection. -/
theorem public_resume_has_sufficient_fuel
    {outputParameter outputResult : TypeSystem.Ty}
    (functionResult : header.function.resultType = .function outputParameter outputResult)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation header.function.context ⟨[]⟩
      (.global function) arguments (.value sourceResult) after) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
      (payload : Core.Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      (∀ executionFuel, required ≤ executionFuel →
        nativeCheckpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions rootOwner caller header capture header.function.context (.value sourceResult) after
        (.inRight .word payload) finalStore finalMap finalWorld rootFaults ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → 1 ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : SourceCoreIndexedSession.Completion nativeArtifact)
          (generation : SourceCorePublicValues.ExportGeneration) (handle : SourceCorePublicValues.Handle)
          (reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore),
          outcome = .succeeded publicCompletion ∧ publicCompletion.value = .function handle ∧
          handle.sourceType = header.function.resultType ∧
          nativeCheckpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧ Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry header actual.session finalMap finalWorld after finalStore reached
            [⟨header.function.resultType, sourceResult, handle, payload, header.output, outputFuel⟩] ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds.initial_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (profile := profile)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := .refl publicSession)
      (atSession := atSession) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled)
      (wellFormed := wellFormed) (selected := selected) (owner := owner recipe.compiled)
      (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt)
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports header header wellFormed).2) trace
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, required ≤ executionFuel →
      nativeCheckpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound)
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult] at requested
  have nativeReady := atSession.exportsReady_iff.mp (ready.exportsReady authority)
  have checkpointReady := started.original.initial_registry.exportsReady nativeReady
  have runtimeFunction : SourceCoreRawMetadata.runtimeType header.function.resultType =
      .function (SourceCoreRawMetadata.runtimeType outputParameter) (SourceCoreRawMetadata.runtimeType outputResult) := by
    rw [functionResult]
    rfl
  refine ⟨caller, capture, payload, finalStore, finalMap, finalWorld, required, completes, result, ?_⟩
  intro executionFuel outputFuel outcome bound positive resumed
  have completed := completes executionFuel bound
  obtain ⟨publicCompletion, handle, outcomeEq, handleValue, handleType, _publicReady⟩ :=
    resumed.runtime_function_succeeded atCheckpoint checkpointReady completed requested runtimeFunction (by omega)
  have actualResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion) := outcomeEq ▸ resumed
  obtain ⟨actual, generation, actualValue, actualStore, actualCompleted, succeeded,
      valueAt, typeAt, fuelAt, sessionAt⟩ := actualResume.indexed_succeeded atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, returnedSource, returnedPayload, sourceEq, nativeEq, related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_remembered rfl started selected requested succeeded result
      (valueAt.symm.trans handleValue)
  cases Staging.Recursive.Outcome.value.inj sourceEq
  have payloadEq : payload = returnedPayload := (Core.Value.inRight.inj nativeEq).2
  cases payloadEq
  exact ⟨publicCompletion, actual, generation, handle, reached, outcomeEq, handleValue, handleType, succeeded,
    ⟨valueAt, typeAt, fuelAt, sessionAt⟩, related, retained,
    started.returned_registry succeeded, succeeded.exportsReady checkpointReady⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedFunctionPreservation
