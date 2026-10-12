import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectClosureApplicationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicStartMeaning

/-! The actual direct-handle checkpoint supplies selection, packed input and
native execution. Retained Source meaning is taken from the current caller,
then the established body family reflects that same native application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

/-- The actual packed Unit encoder and authenticated selection determine the
complete initial native call. No payload representation is assumed here. -/
theorem unit_initial {recipe : Recipe} {artifact : Artifact} {session : Session artifact}
    {handle : SourceCorePublicValues.Handle} {checkpoint : Checkpoint artifact} {fuel oldFuel : Nat}
    {result : TypeSystem.Ty} {native : Core.Value} {world : StoreTyping} {store : Store}
    (atRecipe : ArtifactRecipe artifact recipe)
    (nativeAt : session.NativeAt world store)
    (handleType : handle.sourceType = .function .unit result)
    (imported : session.EncodesAt oldFuel (.function .unit result) (.function handle) native)
    (started : checkpoint.HandleStart session handle .unit fuel) :
    ∃ nativeResult,
      recipe.compiled.compatible.checked.catalog.project result = .ok nativeResult ∧
      checkpoint.ResultTypeAt result ∧ checkpoint.PayloadTypeAt nativeResult ∧
      native.type = CallableContract.functionType .unit nativeResult ∧
      CheckpointInitial checkpoint CallableIndexedLambdaCalls.applyPayload
        (native :: .unit :: SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  obtain ⟨parameter, actualResult, nativeParameter, nativeResult, callable, registry, raw, encodedValues,
    selected, _registryAt, encoded, _valuesAt, _rawRegistry, _owner, _typed, requested, payloadType, initial⟩ := started.details
  obtain ⟨rfl, rfl⟩ := selected.signature handleType
  have nativeParameterEq : nativeParameter = .unit :=
    (Except.ok.inj selected.spec.2.2.1).symm
  have callableEq := selected.callable_eq imported
  have packedEq := encoded.unit
  have typed := selected.spec.2.2.2.2.2.1.type_eq
  rw [nativeParameterEq, callableEq] at typed
  refine ⟨nativeResult, selected.spec.2.2.2.1, requested, payloadType, typed, ?_⟩
  cases session
  rename_i sessionAuthority actualWorld actualStore stored environmentTyped slots values owner sourcePrefix
  change actualWorld = world ∧ actualStore = store at nativeAt
  rcases nativeAt with ⟨rfl, rfl⟩
  rw [callableEq, packedEq] at initial
  cases checkpoint
  exact initial

/-- The facade's accepted start selects the same indexed session and original
checkpoint, without starting a second invocation. -/
theorem recover_handle_start {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {artifact : Artifact} {session : Session artifact}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value} {fuel : Nat}
    (atSession : publicSession.IndexedAt session)
    (accepted : publicSession.startHandlePacked handle argument fuel = .ok publicCheckpoint) :
    ∃ checkpoint : Checkpoint artifact,
      publicCheckpoint.IndexedAt checkpoint ∧ checkpoint.HandleStart session handle argument fuel := by
  rcases publicArtifact with ⟨publicCompiled, opened⟩
  cases opened with
  | empty selected => exact False.elim atSession
  | indexed actualRecipe selected actualArtifact recipeAt =>
    rcases publicSession with ⟨actualSession⟩
    rcases atSession with ⟨rfl, sameSession⟩
    have same : actualSession = session := eq_of_heq sameSession
    subst actualSession
    obtain ⟨foundRecipe, foundArtifact, foundSession, checkpoint,
      _openedAt, atFound, atCheckpoint, startEq⟩ :=
      SourceCoreExecution.Session.startHandlePacked_indexed (compiled := publicCompiled)
        (checkpoint := publicCheckpoint) rfl accepted
    have artifactEq : actualArtifact = foundArtifact := atFound.1
    cases artifactEq
    have sessionEq : session = foundSession := eq_of_heq atFound.2
    cases sessionEq
    exact ⟨checkpoint, atCheckpoint, Session.startHandlePacked_receipt session startEq⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Closure} {native : Core.Value} {result : TypeSystem.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function .unit result))
  {nativeType : Core.Ty}
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world (.function .unit result) (.closure function) native
    nativeType)
  (parameters : function.parameters = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable {recipe : Recipe} {artifact : Artifact} {session : Session artifact}
  {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
  {inputFuel oldFuel : Nat}
  (prepared : Recipe.prepare compiled = .ok recipe)
  (atRecipe : ArtifactRecipe artifact recipe)
  (nativeAt : session.NativeAt world store)
  (handleType : handle.sourceType = .function .unit result)
  (imported : session.EncodesAt oldFuel (.function .unit result) (.function handle) native)

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated parameters heaps
  prepared atRecipe nativeAt handleType imported in
/-- Finite completion of the actual direct checkpoint constructs an independent
Source application and the complete returned caller postcondition. -/
theorem completed_reflects_unit
    (started : checkpoint.HandleStart session handle .unit inputFuel)
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ nativeResult,
      compiled.compatible.checked.catalog.project result = .ok nativeResult ∧
      checkpoint.ResultTypeAt result ∧ checkpoint.PayloadTypeAt nativeResult ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.closure function) [] outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨nativeResult, projected, requested, payloadType, nativeTypeEq, initial⟩ :=
    unit_initial atRecipe nativeAt handleType imported started
  have typeEq : nativeType = CallableContract.functionType .unit nativeResult :=
    calleeRelated.runtime_hasType.type_eq.symm.trans nativeTypeEq
  have related := calleeRelated
  rw [typeEq] at related
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (initial.native_done_iff.mp completed))
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectClosureApplicationBounds.reflects_unit receiver stagePrepared profile
      observations extension semantic family namedTerminals namedSupport wellFormed caller stable runtime
      heapTyped calleeTyped related parameters heaps (invocation := invocation) measured
  exact ⟨nativeResult, projected, requested, payloadType, sourceSize, outcome, after, finalMap, finalWorld,
    trace, resultAt⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated parameters heaps
  prepared atRecipe nativeAt handleType imported in
/-- One successful public invokePacked call retains its actual indexed start,
export, value and session alongside independent Source execution. -/
theorem public_invoke_succeeded_reflects_unit
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt handle .unit options (.ok (.succeeded publicCompletion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (nativeResult : Core.Ty) (sourceSize : Nat) (outcome : Staging.Recursive.Outcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping),
      checkpoint.HandleStart session handle .unit options.inputValidationFuel ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      compiled.compatible.checked.catalog.project result = .ok nativeResult ∧
      checkpoint.ResultTypeAt result ∧ checkpoint.PayloadTypeAt nativeResult ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
        invocation context before (.closure function) [] outcome after ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, started⟩ := recover_handle_start atSession accepted
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨nativeResult, projected, requested, payloadType, sourceSize, outcome, after, finalMap, finalWorld,
    trace, resultAt⟩ :=
    completed_reflects_unit receiver stagePrepared profile observations extension semantic family
      namedTerminals namedSupport wellFormed caller stable runtime heapTyped calleeTyped calleeRelated
      parameters heaps prepared atRecipe nativeAt handleType imported started completed invocation
  exact ⟨checkpoint, actual, generation, value, finalStore, nativeResult, sourceSize, outcome, after, finalMap, finalWorld,
    started, exported, ⟨valueEq, typeEq, budgetEq, sessionAt⟩, projected, requested, payloadType, trace, resultAt⟩
end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
