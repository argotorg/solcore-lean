import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRootSourceSignature
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! Independent successful Source execution of the first named entry reaches
the public boundary at sufficient execution and output fuel. Actual bootstrap
and input encoding produce the initial state and receiving metadata; neither
a native execution result nor successful output decoding is a premise. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedOutputPreservation
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
  (baseRegistry : completion.result.context.registry = compiled.compatible.checked.staticRegistry)
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
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope}

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile

include distinct receiver observations baseRegistry semantic family namedTerminals namedSupport wellFormed
  prepared selected opened fresh ready authority atSession atCheckpoint started inputReceipts sourceAt in
/-- Bootstrap and actual input encoding construct the initial heap and argument
relation. General Source success supplies independent execution and export
bounds. The genuine returned session starts a reusable history. -/
theorem public_resume_has_sufficient_fuel
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation header.function.context ⟨[]⟩
      (.global function) arguments (.value sourceResult) after) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, nativeCheckpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
      (payload : Core.Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (requiredExecution requiredOutput : Nat),
      (∀ executionFuel, requiredExecution ≤ executionFuel →
        nativeCheckpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := receiving.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions rootOwner caller header capture header.function.context (.value sourceResult) after
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
            receiving.result.context.registry header actual.session finalMap finalWorld after finalStore reached [] ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  have atRecipe : nativeArtifact.RecipeAt recipe := by
    cases nativeArtifact
    exact started.recipe_eq
  obtain ⟨receiving, _entryAt, contextAt, issued, diagnostics⟩ :=
    RecursiveNamedPublicCheckpointReceiver.at_prepared_checkpoint started.recipe_eq stagePrepared
      started.values started.owner completion.entry
  have extended : SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry := by
    rw [baseRegistry, contextAt, ← started.owner]
    exact encodedValues.extension
  obtain ⟨program, present, _, _⟩ := CallableIndexedOwnedPublicCallableDiagnostics.of_compiled
    recipe.compiled stagePrepared.present
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds.initial_arguments
      (completion := receiving) (inputs := inputs) (rows := rows) (distinct := distinct) (profile := profile)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := .refl publicSession)
      (atSession := atSession) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
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
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports header header wellFormed).2) trace
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
  have nativeReady := atSession.exportsReady_iff.mp (ready.exportsReady authority)
  have checkpointReady := started.original.initial_registry.exportsReady nativeReady
  obtain ⟨requiredOutput, exports⟩ := publicCheckpoint.output_succeeded_uniform
    atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨receiving, contextAt, issued, extended, diagnostics, caller, capture, payload,
    finalStore, finalMap, finalWorld, requiredExecution, requiredOutput, completes, result, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨publicCompletion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel outputBound outcome resumed
  obtain ⟨reached, related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_success rfl started selected exported result
  exact ⟨publicCompletion, actual, generation, reached, succeeded, exported, actualAt,
    related, retained, started.returned_registry exported, returnedReady⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedOutputPreservation
