import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFailures
import Solcore.Frontend.SourceCoreFailurePreservationReceipts

/-! An actual export error follows successful native and Source execution.
The returned public session retains all earlier handles at that exact after-heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryExportErrors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Native success is reflected from the real export-error receipt. The
Source result and all effects remain available through the returned session. -/
theorem public_resume_export_error
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {error : SourceCoreIndexedSession.Error}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.exportError error publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ (actual : Session artifact) (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.ExportErrorResultAt executionFuel outputFuel generation value finalStore error actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input history atRegistry member entryType input started
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present history
  have semanticAt : ∀ reason token, semanticFaults reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
    intro reason token related
    exact CompatibleRegistryDiagnosticExtension.staged_preserved recipe.compiled
      receiver issued present extended (semantic reason token related)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨actual, generation, value, finalStore, exported, sessionAt⟩ :=
    resumed.indexed_export_error atCheckpoint
  obtain ⟨sources, packing, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects
      (completion := receiving) issued stagePrepared profile observations receiving.result.extension
      semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
      started parameterView.symm metadata exported.1 invocation
  obtain ⟨payload, decoded⟩ := exported.succeeded
  obtain ⟨source, sourceValue, _represented, _heaps, _worldEq, _caller, _related, _stable, _typed, _sourceTyped⟩ :=
    RecursivePublicApplicationResult.returned_value resultAt decoded
  subst outcome
  obtain ⟨reached, related, continued⟩ := retained.after_packed_export_error started.original exported resultAt
  have returnedRegistry : actual.RegistryAt encodedValues.registry :=
    congrArg SourceCoreCompatibleValues.Context.registry (exported.values.trans started.values)
  have returnedReady := exported.exportsReady (started.original.initial_registry.exportsReady exportsReady)
  exact ⟨receiving, contextAt, issued, extended, diagnostics, actual, generation, value, finalStore,
    sources, sourceSize, source, after, finalMap, finalWorld, reached, exported, sessionAt, packing,
    trace, resultAt, related, continued, returnedRegistry, returnedReady⟩

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- An actual public invocation supplies its own startup and export error.
The earlier history continues at the exact successful Source after-heap. -/
theorem public_invoke_export_error
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession returned : SourceCoreExecution.Session publicArtifact}
    {options : SourceCoreExecution.RunOptions} {error : SourceCoreIndexedSession.Error}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.exportError error returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed)
      (checkpoint : Checkpoint artifact) (actual : Session artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.ExportErrorResultAt options.executionFuel options.outputValidationFuel generation value finalStore error actual ∧
      returned.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe history.current.1 imported original
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, actual, generation, value, finalStore,
    sources, sourceSize, source, after, finalMap, finalWorld, reached, exported, sessionAt,
    packing, trace, resultAt, related, retained, registry, ready⟩ :=
    public_resume_export_error receiver stagePrepared profile observations semantic family namedTerminals
      namedSupport wellFormed history entry member entryType input atRegistry exportsReady started
      atCheckpoint resumed invocation
  exact ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult, nativeParameter,
    nativeResult, callable, packed, encodedValues, sources, sourceSize, source, after, finalMap,
    finalWorld, reached, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    exported, sessionAt, packing, trace, resultAt, related, retained, registry, ready⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryExportErrors
