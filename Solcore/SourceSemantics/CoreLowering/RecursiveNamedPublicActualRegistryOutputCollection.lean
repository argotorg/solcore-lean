import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputCollection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension

/-! Selected functions in returned constructor payloads and ordered mapping
rows join the actual session history. Both input and output use their original
codecs; Source meaning comes from the independent completed execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
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

private theorem selected_of_cast {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : Artifact} {session : Session artifact} {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicNestedOutputSelections.Selected checked session
      (same ▸ selection : RecursiveNamedPublicNestedOutputSelections.Selection sourceType second)
      source native type fuel entries) :
    RecursiveNamedPublicNestedOutputSelections.Selected checked session selection source native type fuel entries := by
  cases same
  exact selected

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- The real public invocation appends every selected output function in
payload/row order, including repeated keys and repeated handles. The returned
history uses the same current heap and actual metadata receiver. -/
theorem public_invoke_succeeded_collects
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (selection : RecursiveNamedPublicNestedOutputSelections.Selection result publicCompletion.value)
    (invocation : Staging.Recursive.Scope) :
    ∃ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed)
      (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value) (payload : Core.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      value = .inRight .word payload ∧
      RecursiveNamedPublicNestedOutputSelections.Selected recipe.compiled.compatible.checked actual.session
        selection source payload nativeResult options.outputValidationFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached (entries ++ added) ∧
      actual.session.RegistryAt encodedValues.registry := by
  obtain ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome, after,
    finalMap, finalWorld, _priorReached, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    succeeded, actualAt, packing, trace, resultAt, _priorRelated, _priorHistory, returnedRegistry⟩ :=
    RecursiveNamedPublicActualRegistryReflection.public_invoke_succeeded
      receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
      history entry member entryType input atRecipe atRegistry atSession invoked invocation
  have current := RecursiveNamedPublicHistoryRegistryExtension.extend_history history extended
  have metadata : SourceCoreRawMetadata.Extends receiving.result.context.registry encodedValues.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related, retained⟩ :=
    current.collect_packed_nested_success rfl atRecipe started.original started.requested resultView.symm
      succeeded resultAt returnedRegistry metadata (actualAt.1 ▸ selection)
  have originalSelection := selected_of_cast actualAt.1 selected
  have originalHandles := handles.trans
    (RecursiveNamedPublicNestedOutputSelections.Selection.handles_cast actualAt.1 selection)
  rw [sourceValue] at trace resultAt
  exact ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after,
    finalMap, finalWorld, reached, added, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    succeeded, actualAt, packing, trace, resultAt, nativeValue, originalSelection, originalHandles,
    related, retained, returnedRegistry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection
