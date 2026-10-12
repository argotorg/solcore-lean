import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputPreservation
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicOutputShapes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollection

/-! Source success produces sufficient public execution and export fuel,
then every selected nested output function joins the actual returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation
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
/-- Both execution and output fuel bounds precede the actual resume. A structural
selection over that returned public value retains its functions in payload/row
order at the same Source after-heap, including repeated mapping entries. -/
theorem public_resume_has_sufficient_fuel
    (atRegistry : session.RegistryAt completion.result.context.registry)
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ requiredExecution requiredOutput payload finalStore finalMap finalWorld,
      (∀ executionFuel, requiredExecution ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context
        result nativeResult (.value sourceResult) after (.inRight .word payload) finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded publicCompletion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady ∧
          ∀ selection : RecursiveNamedPublicNestedOutputSelections.Selection result publicCompletion.value,
            ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
              RecursiveNamedPublicNestedOutputSelections.Selected recipe.compiled.compatible.checked actual.session
                selection sourceResult payload nativeResult outputFuel added ∧
              added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
              History headers keys functions receiving.result.context.registry anchor actual.session
                finalMap finalWorld after finalStore reached (entries ++ added) := by
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, requiredExecution, requiredOutput,
      payload, finalStore, finalMap, finalWorld, enough, resultAt, resumes⟩ :=
    RecursiveNamedPublicActualRegistryOutputPreservation.public_resume_has_sufficient_fuel
      receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
      history entry member entryType input atRegistry exportsReady started packing trace atCheckpoint
  have retained := RecursiveNamedPublicHistoryRegistryExtension.extend_history history extended
  have metadata : SourceCoreRawMetadata.Extends receiving.result.context.registry encodedValues.registry := by
    rw [contextAt]
    exact .refl _
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨_parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  refine ⟨receiving, contextAt, issued, extended, diagnostics, requiredExecution, requiredOutput,
    payload, finalStore, finalMap, finalWorld, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨publicCompletion, actual, generation, _priorReached, succeeded, exported, actualAt,
      _priorRelated, _priorHistory, returnedRegistry, returnedReady⟩ :=
    resumes executionFuel outputFuel outcome executionBound outputBound resumed
  refine ⟨publicCompletion, actual, generation, succeeded, exported, actualAt,
    returnedRegistry, returnedReady, ?_⟩
  intro selection
  obtain ⟨reached, source, native, added, sourceValue, nativeValue, selected, handles, related, continued⟩ :=
    retained.collect_packed_nested_success rfl atRecipe started.original started.requested resultView.symm
      exported resultAt returnedRegistry metadata (actualAt.1 ▸ selection)
  have sourceEq := Staging.Recursive.Outcome.value.inj sourceValue
  have nativeEq : payload = native := (Core.Value.inRight.inj nativeValue).2
  cases sourceEq
  cases nativeEq
  have originalSelection : RecursiveNamedPublicNestedOutputSelections.Selected
      recipe.compiled.compatible.checked actual.session selection sourceResult payload nativeResult outputFuel added := selected_of_cast actualAt.1 selected
  have originalHandles := handles.trans
    (RecursiveNamedPublicNestedOutputSelections.Selection.handles_cast actualAt.1 selection)
  exact ⟨reached, added, originalSelection, originalHandles, related, continued⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryOutputCollectionPreservation
