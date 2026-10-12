import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension

/-! The pending public call uses its actual input metadata registry. Earlier
handles and Source captures are retained by forward extension, and diagnostics
are transported from the previous authentic receiver. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
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
/-- A successful public resume reflects to Source at the actual extended
registry, with the returned history ready for the next actual session. -/
theorem public_resume_succeeded
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {executionFuel outputFuel : Nat}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion))
    (invocation : Staging.Recursive.Scope) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends completion.result.context.registry receiving.result.context.registry ∧
      (∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token)) ∧
    SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
    SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (value : Core.Value) (finalStore : Store) (sources : List Dynamic.Value)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.NativeDone executionFuel value finalStore ∧
      checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources outcome after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt encodedValues.registry := by
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
  refine ⟨receiving, contextAt, issued, extended, diagnostics, ?_⟩
  exact RecursiveNamedPublicDirectCallablePublicHistory.public_resume_succeeded
    (completion := receiving) issued stagePrepared profile observations receiving.result.extension
    semanticAt family namedTerminals namedSupport wellFormed retained entry member entryType input
    started metadata atCheckpoint resumed invocation

include receiver stagePrepared profile observations semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- The original public invocation derives startup and the actual future
registry. Arbitrarily nested metadata-bearing inputs use their real encoder;
all previous function entries retain their captures at the reached heap. -/
theorem public_invoke_succeeded
    (atRegistry : session.RegistryAt completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed)
      (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (outcome : Staging.Recursive.Outcome)
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
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources outcome after ∧
      ResultAt (registry := receiving.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld
        (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) ∧
      Relates caller reached ∧
      History headers keys functions receiving.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt encodedValues.registry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe history.current.1 imported original
  obtain ⟨receiving, contextAt, issued, extended, diagnostics, parameterView, resultView,
    actual, generation, value, finalStore, sources, sourceSize, outcome, after,
    finalMap, finalWorld, reached, _completed, succeeded, actualAt, packing, trace,
    resultAt, related, retained, returnedRegistry⟩ :=
    public_resume_succeeded receiver stagePrepared profile observations semantic family namedTerminals
      namedSupport wellFormed history entry member entryType input atRegistry started atCheckpoint resumed invocation
  exact ⟨receiving, checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome,
    after, finalMap, finalWorld, reached, contextAt, issued, extended, diagnostics, started, parameterView, resultView,
    succeeded, actualAt, packing, trace, resultAt, related, retained, returnedRegistry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
