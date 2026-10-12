import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableHistory

/-! The successful public packed-call receipt supplies the original startup
and completion. Current function history and structural input descriptions
close argument meaning and preserve the resulting caller and earlier handles.
Metadata-free trees derive the receiving condition from the actual session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory
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
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- Scalars and handles at arbitrary product depth use their original public
encoding. The actual callable row determines the Source argument vector, including
the distinction between zero parameters and one Unit-valued parameter. -/
theorem public_invoke_succeeded_function_tree
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
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (outcome : Staging.Recursive.Outcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources outcome after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      encodedValues.registry = sourceRegistry ∧ actual.session.RegistryAt sourceRegistry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have current := history.current
  have imported := (current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe current.1 imported original
  have registryEq := started.function_tree_registry simple atRegistry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry := by
    rw [registryEq]
    exact receiving
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨reached, related, returnedHistory⟩ := history.after_packed_success original exported resultAt
  have returnedRegistry := started.returned_registry exported
  rw [registryEq] at returnedRegistry
  exact ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome, after, finalMap,
    finalWorld, reached, started, parameterView, resultView, exported,
    ⟨valueEq, typeEq, budgetEq, sessionAt⟩, packing, trace, resultAt, related, returnedHistory,
    registryEq, returnedRegistry⟩


include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Metadata-bearing packed values use the same public continuation when their
actual encoded registry extends into the receiving registry. The callee's
Source signature follows from history and the original selection. -/
theorem public_resume_succeeded
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {executionFuel outputFuel : Nat}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion))
    (invocation : Staging.Recursive.Scope) :
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
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt encodedValues.registry := by
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  have actualView := started.selected.spec.2.1
  have importedView := imported.function_type
  obtain ⟨parameterView, resultView⟩ :=
    TypeSystem.Ty.function.inj (actualView.symm.trans importedView.symm)
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨reached, related, returnedHistory⟩ := history.after_packed_success started.original exported resultAt
  exact ⟨parameterView, resultView, actual, generation, value, finalStore, sources, sourceSize, outcome,
    after, finalMap, finalWorld, reached, completed, exported, ⟨valueEq, typeEq, budgetEq, sessionAt⟩,
    packing, trace, resultAt, related, returnedHistory, started.returned_registry exported⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory
