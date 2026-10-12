import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs

/-! A Source fault determines the real public failure and reached history at
this call's actual metadata, including effects before the fault. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailurePreservation
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
/-- Every actual resume with enough execution fuel returns the represented
failure and preserves prior handles. Output validation fuel is unrestricted.
The Source argument count must match the callable: pack-equivalent argument
rows with a different count can produce Source-only arity faults. -/
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
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.fault failure) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    ∃ required token finalStore finalMap finalWorld,
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token ∧
      (∀ executionFuel, required ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inLeft nativeResult (.word token)) finalStore) ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context
        result nativeResult (.fault failure) after (.inLeft nativeResult (.word token)) finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel (.inLeft nativeResult (.word token)) finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          History headers keys functions receiving.result.context.registry anchor actual
            finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt encodedValues.registry ∧ actual.ExportsReady := by
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, inputTyped, diagnostics⟩ :=
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
  obtain ⟨imported, _calleeRep, calleeTyped⟩ := history.current.2.2.2.2 entry member
  rw [entryType] at imported calleeTyped
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨value, finalStore, finalMap, finalWorld, required, enough, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.has_sufficient_fuel_at_arity
      (completion := receiving) issued stagePrepared profile observations receiving.result.extension
      semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
      started parameterView.symm metadata packing arity trace
  obtain ⟨token, valueEq, faultRelated⟩ : ∃ token,
      value = .inLeft nativeResult (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token := by
    have represented := resultAt.1
    cases represented with
    | fault related => exact ⟨_, rfl, related⟩
  subst value
  have preserved := Staging.Recursive.FaultPreservation.applies wellFormed
    (RecursiveNamedPublicHistorySourceInputs.header_runtime wellFormed anchor)
    history.current.2.2.2.1 calleeTyped packing inputTyped trace
  have ready := started.original.initial_registry.exportsReady exportsReady
  refine ⟨receiving, contextAt, issued, extended, diagnostics, required, token,
    finalStore, finalMap, finalWorld, faultRelated, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome bound resumed
  have completed := enough executionFuel bound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed rfl
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, returnedHistory⟩ :=
    retained.after_packed_failure started.original failed resultAt preserved.1
  have registry : actual.RegistryAt encodedValues.registry :=
    congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans started.values)
  exact ⟨returned, actual, reached, outcomeEq, failed, returnedAt, related,
    returnedHistory, registry, failed.exportsReady ready⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailurePreservation
