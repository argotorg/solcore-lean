import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory

/-! Direct successful output collection reuses the actual export and full
Source result. Selected function leaves join the same returned history even
when the host request and Source result differ by erased annotations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableOutputHistory
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
variable {completion : SourceCoreCallableIndexedPrograms.Completion recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.Support headers keys bodyRegistry header
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
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics


private theorem selected_of_cast {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : RecursiveNamedPublicOutputSelections.Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicOutputSelections.Selected
      (same ▸ selection : RecursiveNamedPublicOutputSelections.Selection sourceType second)
      source native type fuel entries) :
    RecursiveNamedPublicOutputSelections.Selected selection source native type fuel entries := by
  cases same
  exact selected

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- The public invocation keeps all previous handles and appends the selected
function leaves of this same actual output. No Source representation or raw
result equality is supplied by the caller. -/
theorem public_invoke_succeeded_collects_function_tree
    {sourceRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : session.RegistryAt sourceRegistry)
    (receiving : SourceCoreRawMetadata.Extends sourceRegistry completion.result.context.registry)
    (simple : FunctionTreeSimple argument)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (selection : RecursiveNamedPublicOutputSelections.Selection result publicCompletion.value)
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value) (payload : Core.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld callFaults ∧
      value = .inRight .word payload ∧
      RecursiveNamedPublicOutputSelections.Selected selection source payload nativeResult options.outputValidationFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached (entries ++ added) ∧
      encodedValues.registry = sourceRegistry ∧ actual.session.RegistryAt sourceRegistry := by
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome, after,
      finalMap, finalWorld, _previousReached, started, parameterView, resultView, succeeded, actualAt,
      packing, trace, resultAt, _previousRelated, _previousHistory, registryEq, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectCallablePublicHistory.public_invoke_succeeded_function_tree
      receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
      history entry member entryType input atRecipe atRegistry receiving simple atSession invoked invocation
  obtain ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related, retained⟩ :=
    history.collect_packed_success started.original started.requested resultView.symm succeeded resultAt
      (actualAt.1 ▸ selection)
  have originalSelection := selected_of_cast actualAt.1 selected
  have originalHandles := handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast actualAt.1 selection)
  rw [sourceValue] at trace resultAt
  exact ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult, nativeParameter,
    nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after, finalMap,
    finalWorld, reached, added, started, parameterView, resultView, succeeded, actualAt, packing, trace,
    resultAt, nativeValue, originalSelection, originalHandles, related, retained, registryEq, returnedRegistry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableOutputHistory
