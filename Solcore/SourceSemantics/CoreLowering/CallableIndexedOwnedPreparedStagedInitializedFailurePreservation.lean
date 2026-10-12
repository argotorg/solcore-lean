import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation
import Solcore.Frontend.SourceCoreFailurePreservationReceipts

/-! An independent staged Source fault supplies a native fuel bound and fixes
an actual public failure token. Every genuine resume above that bound returns
the same Source after-heap and an initial reusable History. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedFailurePreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association (headers rows) (keys compiled) bodyRegistry semanticFaults
      mapping world function native bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers rows → Body header)
  (namedSupport : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (keys compiled) bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {recipe : SourceCoreIndexedSession.Recipe}
  (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
  {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
  {bootstrapSession publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {bootstrapFuel : Nat} {options : SourceCoreExecution.RunOptions}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
  (fresh : publicBootstrap.FreshAt)
  (ready : publicBootstrap.ReadyAt bootstrapFuel bootstrapSession)
  (sameRuntime : bootstrapSession.SameRuntime publicSession)
  (atSession : publicSession.IndexedAt nativeSession)
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  {arguments : List Dynamic.Value}
  (inputReceipts : RecursiveNamedPublicNestedInputs.Inputs rows nativeSession
    header.function.context (header.bindings.map (fun binding => binding.1.scheme.body))
    publicArguments arguments)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope}

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include distinct receiver observations extension semantic family namedTerminals namedSupport wellFormed
  prepared selected opened fresh ready sameRuntime atSession atCheckpoint started inputReceipts metadata sourceAt in
/-- The Source fault produces native completion; no native completed-result
premise is supplied. Actual public resume receipts retain the resulting session
and History at any output-validation budget. Diagnostic tokens need not be
injective: the conclusion keeps the original Source/token relation. -/
theorem public_resume_has_sufficient_fuel
    {sourceSize : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation header.function.context ⟨[]⟩
      (.global function) arguments (.fault failure) after) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
    ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
      (token : Word) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
      rootFaults failure token ∧
      (∀ executionFuel, required ≤ executionFuel →
        nativeCheckpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore) ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := completion.result.context.registry) (payloads := payloads)
        (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
        rootFunctions rootOwner caller header capture header.function.context (.fault failure) after
        (.inLeft header.output (.word token)) finalStore finalMap finalWorld rootFaults ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact)
          (actual : SourceCoreIndexedSession.Session nativeArtifact)
          (reached : RecursiveNamedPublicFunctionHistory.Caller rootHeaders rootKeys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          nativeCheckpoint.FailedResultAt executionFuel (.inLeft header.output (.word token)) finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          RecursiveNamedPublicFunctionHistory.History rootHeaders rootKeys rootFunctions
            completion.result.context.registry header actual finalMap finalWorld after finalStore reached [] ∧
          actual.RegistryAt encodedValues.registry := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedNestedPublicBounds.initial_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (profile := profile)
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := sameRuntime)
      (atSession := atSession) (started := started) (inputReceipts := inputReceipts) (metadata := metadata)
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, required, enough, result⟩ :=
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.preserves_root
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared recipe.compiled)
      (wellFormed := wellFormed) (selected := selected) (owner := owner recipe.compiled)
      (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt)
      (supports := (RecursiveNamedPublicReturnedValues.header_context_supports header header wellFormed).2) trace
  obtain ⟨token, valueEq, faultRelated⟩ : ∃ token,
      value = .inLeft header.output (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics failure token := by
    have representation := result.2.1
    cases representation with
    | fault related => exact ⟨_, rfl, related⟩
  subst value
  have completes : ∀ executionFuel, required ≤ executionFuel →
      nativeCheckpoint.NativeDone executionFuel (.inLeft header.output (.word token)) finalStore :=
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound)
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack arguments
  have preserved := Staging.Recursive.FaultPreservation.applies wellFormed
    (RecursiveNamedPublicHistorySourceInputs.header_runtime wellFormed header) heapTyped
    (RecursiveNamedPublicHistorySourceInputs.source_typed wellFormed sourceAt header ⟨[]⟩)
    packing (packing.hasType argumentsTyped) trace
  refine ⟨caller, capture, token, finalStore, finalMap, finalWorld, required, faultRelated, completes, result, ?_⟩
  intro executionFuel outputFuel outcome bound resumed
  have completed := completes executionFuel bound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed rfl
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_failure rfl started selected failed result preserved.1
  have returnedRegistry : actual.RegistryAt encodedValues.registry := by
    have values := failed.2.2.2.2.1.trans started.values
    cases nativeCheckpoint
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  exact ⟨returned, actual, reached, outcomeEq, failed, returnedAt, related, retained, returnedRegistry⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedFailurePreservation
