import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableHistory
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation

/-! Direct language failure retains old handles in the actual returned session.
The original public completion and independent fault preservation derive the
Source fault and final heap typing, including effects before the failure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFailures
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
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- A genuine failed public resumption reflects to Source and keeps earlier
captures at its returned heap without a final heap typing premise. -/
theorem public_resume_failed_at_arity
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {reason : Word}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed reason publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel value finalStore reason actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry := by
  obtain ⟨imported, _represented, calleeTyped⟩ := history.current.2.2.2.2 entry member
  rw [entryType] at imported
  rw [entryType] at calleeTyped
  have actualView := started.selected.spec.2.1
  have importedView := imported.function_type
  obtain ⟨parameterView, _resultView⟩ :=
    TypeSystem.Ty.function.inj (actualView.symm.trans importedView.symm)
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects_at_arity receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := resultAt.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  obtain ⟨_packedRelated, packedTyped⟩ := started.history_input_compatible history input parameterView metadata
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate anchor wellFormed
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have preserved := Staging.Recursive.FaultPreservation.applies wellFormed runtime history.current.2.2.2.1
    calleeTyped packing packedTyped trace
  obtain ⟨reached, related, retained⟩ :=
    history.after_packed_failure started.original failed resultAt preserved.1
  have registry : actual.RegistryAt encodedValues.registry := by
    have same := failed.2.2.2.2.1
    have values := started.values
    exact congrArg SourceCoreCompatibleValues.Context.registry (same.trans values)
  exact ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld,
    reached, failed, sessionAt, packing, arity, trace, resultAt, related, retained, registry⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
theorem public_resume_failed
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {reason : Word}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed reason publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel value finalStore reason actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry := by
  obtain ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, sessionAt, packing, _arity, rest⟩ := public_resume_failed_at_arity
    receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
      wellFormed history entry member entryType input started metadata atCheckpoint resumed invocation
  exact ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, sessionAt, packing, rest⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- Actual public invocation recovers its own startup and failed resumption.
Inputs consisting of scalars, handles and products derive metadata identity. -/
theorem public_invoke_failed_function_tree
    {sourceRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : session.RegistryAt sourceRegistry)
    (receiving : SourceCoreRawMetadata.Extends sourceRegistry completion.result.context.registry)
    (simple : FunctionTreeSimple argument)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession returned : SourceCoreExecution.Session publicArtifact}
    {options : SourceCoreExecution.RunOptions} {reason : Word}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Session artifact)
      (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      encodedValues.registry = sourceRegistry ∧ actual.RegistryAt sourceRegistry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe history.current.1 imported original
  have registryEq := started.function_tree_registry simple atRegistry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry := by
    rw [registryEq]
    exact receiving
  obtain ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld,
    reached, failed, sessionAt, packing, trace, resultAt, related, retained, registry⟩ :=
    public_resume_failed receiver stagePrepared profile observations extension semantic family namedTerminals
      namedSupport wellFormed history entry member entryType input started metadata
      atCheckpoint resumed invocation
  rw [registryEq] at registry
  exact ⟨checkpoint, actual, value, finalStore, actualParameter, actualResult, nativeParameter,
    nativeResult, callable, packed, encodedValues, sources, sourceSize, failure, after, finalMap,
    finalWorld, reached, started, parameterView, resultView, failed, sessionAt, packing,
    trace, resultAt, related, retained, registryEq, registry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFailures
