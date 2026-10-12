import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableHistory
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues

/-! Independent successful Source execution of function-valued calls closes
the actual public export and adds that function to the same returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFunctionPreservation
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
  (extension : SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry
    completion.result.context.registry)
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
  {parameter outputParameter outputResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter (.function outputParameter outputResult))
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)


local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem selected_function {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle)
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} :
    RecursiveNamedPublicOutputSelections.Selected
      (same.symm ▸ (RecursiveNamedPublicOutputSelections.Selection.function (type := type)))
      source native nativeType fuel [⟨type, source, handle, native, nativeType, fuel⟩] := by
  cases same
  exact .function

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Actual Source execution implies public function export for every sufficient
native budget and every positive output budget. The authentic issuer/slot
receipt is supplied by initialization and retained by real session events. -/
theorem public_resume_has_sufficient_fuel
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ required payload finalStore finalMap finalWorld,
      (∀ executionFuel, required ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context
        (.function outputParameter outputResult) nativeResult
        (.value sourceResult) after (.inRight .word payload) finalStore finalMap finalWorld callFaults ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → 1 ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
          (handle : SourceCorePublicValues.Handle)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded publicCompletion ∧ publicCompletion.value = .function handle ∧
          handle.sourceType = actualResult ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧ Relates caller reached ∧
          History headers keys functions completion.result.context.registry anchor actual.session
            finalMap finalWorld after finalStore reached
            (entries ++ [⟨.function outputParameter outputResult, sourceResult, handle, payload, nativeResult, outputFuel⟩]) ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady := by
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨value, finalStore, finalMap, finalWorld, required, enough, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.has_sufficient_fuel receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata packing trace
  have success : ∃ payload, value = .inRight .word payload := by
    have represented := resultAt.1
    cases represented with
    | value related => exact ⟨_, rfl⟩
  obtain ⟨payload, rfl⟩ := success
  have ready := started.original.initial_registry.exportsReady exportsReady
  refine ⟨required, payload, finalStore, finalMap, finalWorld, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome bound outputBound resumed
  have completed := enough executionFuel bound
  obtain ⟨publicCompletion, handle, succeeded, publicValue, sourceType, _publicReady⟩ :=
    resumed.runtime_function_succeeded atCheckpoint ready completed started.requested resultView (by omega)
  have actualResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion) :=
    succeeded ▸ resumed
  obtain ⟨actual, generation, actualValue, actualStore, actualCompleted, exported,
      valueAt, sourceAt, fuelAt, sessionAt⟩ := actualResume.indexed_succeeded atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, post⟩ := resultAt.2.2.2.2.2.2
  have actualValue : actual.value = .function handle := valueAt.symm.trans publicValue
  let selection : RecursiveNamedPublicOutputSelections.Selection (.function outputParameter outputResult) actual.value :=
    actualValue.symm ▸ .function
  have selected : RecursiveNamedPublicOutputSelections.Selected selection sourceResult payload nativeResult outputFuel
      [⟨.function outputParameter outputResult, sourceResult, handle, payload, nativeResult, outputFuel⟩] := by
    exact selected_function actualValue
  have retained := History.packed_next history started.original exported resultAt reached ⟨related, post⟩
    (.selectCompatible started.requested resultView.symm rfl rfl selection selected)
  exact ⟨publicCompletion, actual, generation, handle, reached, succeeded, publicValue, sourceType, exported,
    ⟨valueAt, sourceAt, fuelAt, sessionAt⟩, related, retained, started.returned_registry exported,
    exported.exportsReady ready⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFunctionPreservation
