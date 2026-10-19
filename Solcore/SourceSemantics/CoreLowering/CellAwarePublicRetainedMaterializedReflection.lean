import Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedHandle
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectFailure
import Solcore.SourceSemantics.Staging.RecursiveCallableErasure
import Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedFaultHeap

/-! Observed public handle completion reconstructs independent Source meaning
from its authentic retained materialized row and actual current public inputs.
Both success and failure retain the exact reached physical state and history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open CellAwarePublicApplicationResult (ResultAt)
open GeneralizedLocalMaterializedAssociation

variable {recipe : Recipe}
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial recipe.compiled.compatible.checked).registry
    completion.result.context.registry)
  (bodyTyping : SelectedCompilationBodyTyping.Bodies recipe.compiled)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells :=
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    ) (receiving := completion.result.context.registry) (anchor := anchor)
    session mapping world before store caller entries)
  (entry : Entry) (inHistory : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : Dynamic.Closure} (sourceEq : entry.source = .closure function)
  (retained : CellAwareMaterializedRetainedEntries.EntryAt keys mapping world entry)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "rootCells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable {publicArtifact : SourceCoreExecution.Artifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  (exactRegistry : completion.result.context.registry = encodedValues.registry)
  (exportsReady : session.ExportsReady)

structure Succeeded (executionFuel outputFuel : Nat)
    (publicCompletion : SourceCoreExecution.Completion publicArtifact) (invocation : Staging.Recursive.Scope) where
  actual : Completion artifact
  generation : SourceCorePublicValues.ExportGeneration
  native : Core.Value
  finalStore : Store
  sources : List Dynamic.Value
  packing : Dynamic.ValuesPack sources packedSource
  arity : sources.length = function.parameters.length
  size : Nat
  source : Dynamic.Value
  after : Dynamic.Heap
  finalMap : LocationMap
  finalWorld : StoreTyping
  reached : Caller headers keys finalMap finalWorld after finalStore
  completed : checkpoint.NativeDone executionFuel native finalStore
  exported : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual
  atCompletion : publicCompletion.IndexedAt actual
  trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages size invocation
    anchor.function.context before entry.source sources (.value source) after
  plain : Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
    invocation.evidence (Staging.Recursive.callableEvidence entry.source) before entry.source sources source after
  result : ResultAt (registry := completion.result.context.registry) functions rootCells caller anchor.function.context result nativeResult
    (.value source) after native finalStore finalMap finalWorld callFaults
  related : CallableIndexedOwnedFunctionState.Relates caller reached
  history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := rootCells)
    (receiving := completion.result.context.registry) (anchor := anchor)
    actual.session finalMap finalWorld after finalStore reached entries
  registry : actual.session.RegistryAt completion.result.context.registry
  exports : actual.session.ExportsReady

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started
  parameterView metadata atCheckpoint exactRegistry exportsReady in
/-- A successful public resume recovers the exact ordinary Source call, without
a Source execution or closure association supplied by the caller. -/
theorem succeeded {executionFuel outputFuel : Nat}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion))
    (invocation : Staging.Recursive.Scope) :
    Nonempty (Succeeded (completion := completion) (caller := caller) (anchor := anchor) (result := result) (function := function) (packedSource := packedSource)
      (entry := entry) (entries := entries) (nativeResult := nativeResult) (checkpoint := checkpoint)
      functions executionFuel outputFuel publicCompletion invocation) := by
  obtain ⟨actual, generation, native, finalStore, completed, exported, atReturned⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, arity, size, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    CellAwarePublicRetainedMaterializedHandle.completed_reflects functions profile receiver extension bodyTyping wellFormed
      history.semantic entry inHistory entryType sourceEq retained input started parameterView metadata completed invocation
  obtain ⟨payload, decoded, _imported⟩ := exported.reimports
  obtain ⟨source, outcomeEq, _represented, _heaps, _world, _returned, _related, _stable, _heapTyped, _typed⟩ :=
    CellAwarePublicApplicationResult.returned_value resultAt decoded
  subst outcome
  obtain ⟨reached, related, retainedHistory⟩ := history.semantic.after_packed_success started.original exported resultAt
  exact ⟨⟨actual, generation, native, finalStore, sources, packing, arity, size, source, after, finalMap, finalWorld,
    reached, completed, exported, atReturned, trace, trace.sound.value_plain, resultAt, related,
    ⟨retainedHistory, history.physical.extend resultAt.2.2.2.2.1⟩,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady exportsReady)⟩⟩

structure Failed (executionFuel : Nat) (token : Word)
    (publicReturned : SourceCoreExecution.Session publicArtifact) (invocation : Staging.Recursive.Scope) where
  actual : Session artifact
  native : Core.Value
  finalStore : Store
  sources : List Dynamic.Value
  packing : Dynamic.ValuesPack sources packedSource
  arity : sources.length = function.parameters.length
  size : Nat
  failure : Staging.Recursive.Failure
  after : Dynamic.Heap
  finalMap : LocationMap
  finalWorld : StoreTyping
  reached : Caller headers keys finalMap finalWorld after finalStore
  completed : checkpoint.NativeDone executionFuel native finalStore
  failed : checkpoint.FailedResultAt executionFuel native finalStore token actual
  atSession : publicReturned.IndexedAt actual
  trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages size invocation
    anchor.function.context before entry.source sources (.fault failure) after
  plain : ∀ reason, failure = .semantic reason →
    Dynamic.CallableFaults (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
      invocation.evidence (Staging.Recursive.callableEvidence entry.source) before entry.source sources reason after
  result : ResultAt (registry := completion.result.context.registry) functions rootCells caller anchor.function.context result nativeResult
    (.fault failure) after native finalStore finalMap finalWorld callFaults
  fault : callFaults failure token
  heap : Dynamic.HeapWellTyped anchor.function.context after
  related : CallableIndexedOwnedFunctionState.Relates caller reached
  history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := rootCells)
    (receiving := completion.result.context.registry) (anchor := anchor)
    actual finalMap finalWorld after finalStore reached entries
  registry : actual.RegistryAt completion.result.context.registry
  exports : publicReturned.ExportsReady

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started
  parameterView metadata atCheckpoint exactRegistry exportsReady in
/-- The failed public event recovers its real staged fault and reached heap.
When the fault is semantic, erasure yields the independent Source fault. -/
theorem failed {executionFuel outputFuel : Nat} {token : Word}
    {publicReturned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token publicReturned))
    (invocation : Staging.Recursive.Scope) :
    Nonempty (Failed (completion := completion) (caller := caller) (anchor := anchor) (result := result) (function := function) (packedSource := packedSource)
      (entry := entry) (entries := entries) (nativeResult := nativeResult) (checkpoint := checkpoint)
      functions executionFuel token publicReturned invocation) := by
  obtain ⟨actual, _generation, native, finalStore, completed, failedAt, atReturned⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨sources, packing, arity, size, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    CellAwarePublicRetainedMaterializedHandle.completed_reflects functions profile receiver extension bodyTyping wellFormed
      history.semantic entry inHistory entryType sourceEq retained input started parameterView metadata completed invocation
  obtain ⟨failure, outcomeEq, fault⟩ : ∃ failure, outcome = .fault failure ∧ callFaults failure token := by
    have related := resultAt.1
    have decoded := failedAt.2.1
    cases related with
    | value _ => cases decoded
    | fault related =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
        subst token
        exact ⟨_, rfl, related⟩
  subst outcome
  have afterTyped := CellAwarePublicMaterializedFaultHeap.after_fault functions bodyTyping wellFormed history.semantic
    entry inHistory entryType input started parameterView metadata packing trace
  obtain ⟨reached, related, retainedHistory⟩ := history.semantic.after_packed_failure
    started.original failedAt resultAt afterTyped
  have returnedRegistry : actual.RegistryAt completion.result.context.registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failedAt.2.2.2.2.1.trans started.values)
  exact ⟨⟨actual, native, finalStore, sources, packing, arity, size, failure, after, finalMap, finalWorld,
    reached, completed, failedAt, atReturned, trace,
    (fun reason same => (same ▸ trace.sound).semanticFault_plain), resultAt, fault, afterTyped, related,
    ⟨retainedHistory, history.physical.extend resultAt.2.2.2.2.1⟩, returnedRegistry,
    atReturned.exportsReady_iff.mpr (failedAt.exportsReady
      (started.original.initial_registry.exportsReady exportsReady))⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedReflection
