import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.PublicHistories
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryFailures
import Solcore.Core.ExactFuelProperties
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.MaterializedExpressions
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.MaterializedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.BodyEntries
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicCheckpointReceiver
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.ReadEffects
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Generalized.LambdaCompilation
import Solcore.SourceSemantics.CoreLowering.PublicSessions
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalFrontdoor
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
import Solcore.SourceSemantics.CoreLowering.AcceptedStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.CellAware.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures

/-!
# Cell-aware public handles and starts

Public starts, and calls through handles: packed inputs, builtin and materialized handles, observed outputs and failures, and registry extension of a session.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectFailure
/-! A direct handle call retains its actual mixed heap and prior public history.
The original requested signature and output codec determine public completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectFailure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header)
open CellAwarePublicFunctionHistory (Caller)
open CellAwarePublicApplicationResult (ResultAt)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  {parameter requested sourceResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value}
  (started : StartAt session handle argument inputFuel checkpoint recipe world store
    parameter requested nativeParameter nativeResult callable packed encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {failure : Staging.Recursive.Failure} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : ResultAt (registry := registry) functions cells caller anchor.function.context sourceResult nativeResult
    (.fault failure) after native finalStore finalMap finalWorld faults)
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)

include started exactRegistry ready atCheckpoint result completes in
theorem failed :
    ∃ token, faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ actual.RegistryAt registry ∧ actual.ExportsReady := by
  obtain ⟨token, nativeEq, represented⟩ : ∃ token,
      native = .inLeft nativeResult (.word token) ∧ faults failure token := by
    have related := result.1
    cases related with
    | fault represented => exact ⟨_, rfl, represented⟩
  have checkpointReady := started.original.initial_registry.exportsReady ready
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  have completed := completes executionFuel enough
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed (by rw [nativeEq]; rfl)
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failedAt, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  have returnedRegistry : actual.RegistryAt registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failedAt.2.2.2.2.1.trans started.values)
  exact ⟨returned, actual, outcomeEq, failedAt, returnedAt, returnedRegistry, failedAt.exportsReady checkpointReady⟩

include started exactRegistry ready atCheckpoint result completes in
theorem after_failure {entries : List Entry}
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after)
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ token, faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt registry ∧ returned.ExportsReady := by
  obtain ⟨token, represented, output⟩ :=
    failed functions cells started exactRegistry ready atCheckpoint result completes
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, failedOutcome, actualResult, actualAt, registryAt, actualReady⟩ :=
    output executionFuel outputFuel outcome enough resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_failure
    started.original actualResult result heapTyped
  exact ⟨returned, actual, reached, failedOutcome, actualResult, actualAt, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩, registryAt, actualAt.exportsReady_iff.mpr actualReady⟩


include started exactRegistry ready atCheckpoint result in
/-- An observed failed direct call retains the exact Source-derived final heap
and every earlier handle even if the observer used a different execution budget. -/
theorem observed_failure {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries)
    (heapTyped : Dynamic.HeapWellTyped anchor.function.context after)
    {proofFuel executionFuel outputFuel : Nat}
    (completed : checkpoint.NativeDone proofFuel native finalStore)
    {token : Word} {returned : SourceCoreExecution.Session publicArtifact}
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned)) :
    faults failure token ∧
    ∃ (actual : Session artifact) (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
      returned.IndexedAt actual ∧ Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
        (receiving := registry) (anchor := anchor)
        actual finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt registry ∧ returned.ExportsReady := by
  obtain ⟨actual, _generation, observed, observedStore, done, failedAt, returnedAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨_leftSteps, _leftEnough, left⟩ := runStateful_sound completed
  obtain ⟨_rightSteps, _rightEnough, right⟩ := runStateful_sound done
  obtain ⟨_steps, sameValue, sameStore⟩ := left.final_unique right
  cases sameValue
  cases sameStore
  have tokenAt : faults failure token := by
    have represented := result.1
    have decoded := failedAt.2.1
    cases represented with
    | fault represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.failed.injEq] at decoded
        subst token
        exact represented
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_failure
    started.original failedAt result heapTyped
  have checkpointReady := started.original.initial_registry.exportsReady ready
  have returnedRegistry : actual.RegistryAt registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failedAt.2.2.2.2.1.trans started.values)
  exact ⟨tokenAt, actual, reached, failedAt, returnedAt, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩, returnedRegistry,
    returnedAt.exportsReady_iff.mpr (failedAt.exportsReady checkpointReady)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectFailure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
/-! Actual packed input encoding derives every retained function leaf from
its current mixed-cell history, preserving ordered data and repeated handles. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
section Inputs
variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
  {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session handle argument fuel checkpoint recipe world store
    parameter result nativeParameter nativeResult callable packed encodedValues)

include started

/-- Existing history supplies current meanings for every nested handle. The
actual encoder supplies the packed native payload and all registry changes. -/
theorem history_input_compatible
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value} {sourceParameter : TypeSystem.Ty}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      sourceParameter argument source)
    (compatible : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType sourceParameter)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      sourceParameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source sourceParameter := by
  have current := history.current
  obtain ⟨meaning, sourceTyped⟩ := RecursiveNamedPublicFunctionHistoryEncoding.Input.meaning
    receipt started.recipe_eq
    (fun entry member => (current.2.2.2.2 entry member).1)
    (fun entry member => (current.2.2.2.2 entry member).2.1)
    (fun entry member => (current.2.2.2.2 entry member).2.2)
  obtain ⟨before, encoded, _registry, owner, accepted, valueEq, registryEq⟩ := started.raw
  have typed := started.packedTyped
  rw [← valueEq] at typed
  have extended : SourceCoreRawMetadata.Extends encoded.registry receiving := registryEq ▸ metadata
  have represented := meaning owner compatible accepted started.parameterProjection typed extended
  rw [valueEq] at represented
  exact ⟨represented, sourceTyped⟩

/-- Exact source signatures are the reflexive compatibility case. -/
theorem history_input
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value}
    (history : History headers keys functions cells receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument source)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world parameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source parameter :=
  history_input_compatible started history receipt rfl metadata

end Inputs
end Solcore.SourceSemantics.CoreLowering.CellAwarePublicPackedInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicMaterializedFaultHeap
/-! The actual current public input and retained callee supply the deep heap
typing needed after a measured faulting materialized call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicMaterializedFaultHeap
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
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys functions
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    completion.result.context.registry anchor session mapping world before store caller entries)
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

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping selectedBodies history inHistory entryType input started parameterView metadata in
theorem after_fault {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {size : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size invocation
      anchor.function.context before entry.source sources (.fault failure) after) :
    Dynamic.HeapWellTyped anchor.function.context after := by
  have current := history.current
  have typed := (current.2.2.2.2 entry inHistory).2.2
  rw [entryType] at typed
  obtain ⟨_packedRelated, packedTyped⟩ := CellAwarePublicPackedInputs.history_input_compatible
    started history input parameterView.symm metadata
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  exact (Staging.Recursive.SelectedPreservation.applies selectedBodies runtime
    current.2.2.2.1 typed packing packedTyped trace).heap_typed

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicMaterializedFaultHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicMaterializedHandleMeaning
/-! The actual accepted direct-handle checkpoint and current public history
supply input, heap and captured Source typing for a retained materialized row.
Only compiler provenance identifies the row; no call meaning is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicMaterializedHandleMeaning
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
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys functions
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (inHistory : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : Dynamic.Closure} (sourceEq : entry.source = .closure function)
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Core.Ty}
  (association : Association recipe.compiled mapping world function entry.native bindings parameterCore resultCore)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (atFrame : association.AtFrame owner.key.frameLocation)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping in
private theorem anchor_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
    anchor.function.context anchor.function.source := by
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  rw [anchor.frame.context, anchor.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

include history inHistory entryType sourceEq input started parameterView metadata in
private theorem current_inputs :
    callable = entry.native ∧
    Dynamic.ValueHasType anchor.function.context before (.closure function) (.function parameter result) ∧
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      parameter packedSource packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context before packedSource parameter := by
  obtain ⟨imported, _represented, typed⟩ := history.current.2.2.2.2 entry inHistory
  have callableEq := started.callable_eq imported
  rw [entryType, sourceEq] at typed
  obtain ⟨packedRelated, packedTyped⟩ := CellAwarePublicPackedInputs.history_input_compatible started history input parameterView.symm metadata
  exact ⟨callableEq, typed, packedRelated, packedTyped⟩

include bodyTyping history inHistory entryType sourceEq input started parameterView metadata in
/-- Current public history and the accepted packed input recover Source argument
and capture typing at the exact incoming heap. -/
theorem source_arguments {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources := by
  obtain ⟨_callableEq, calleeTyped, _packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨parameterEq, _resultEq, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceTyped := packing.unpackTypes (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  exact CallableIndexedOwnedStoredClosureSourceArguments.at_arguments (anchor_runtime bodyTyping) calleeTyped
    history.current.2.2.2.1 sourceTyped packing parameterEq.symm arity

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- Finite completion of the original public checkpoint reconstructs the
materialized Source call using its current captures and packed input. -/
theorem completed_reflects {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore) (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
          anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨callableEq, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (association.runtime_hasType.type_eq.symm.trans (callableEq ▸ started.callableTyped.type_eq))
  obtain ⟨rfl, rfl⟩ := nativeTypes
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  rw [callableEq] at measured
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    CellAwareMaterializedPackedApplication.reflects functions profile receiver extension caller stable
      (anchor_runtime bodyTyping) selectedBodies heapTyped association owner atFrame calleeTyped packedTyped packedRelated heaps measured
  exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld,
    by simpa only [sourceEq] using trace, resultAt⟩

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- A finite independent Source call supplies sufficient fuel for the same
accepted public checkpoint, including its exact failure store. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
      anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨callableEq, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (association.runtime_hasType.type_eq.symm.trans (callableEq ▸ started.callableTyped.type_eq))
  obtain ⟨rfl, rfl⟩ := nativeTypes
  rw [sourceEq] at trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    CellAwareMaterializedPackedApplication.preserves functions profile receiver extension caller stable
      (anchor_runtime bodyTyping) selectedBodies heapTyped association owner atFrame calleeTyped packedTyped packedRelated heaps
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  rw [← callableEq] at evaluated
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- An ordinary independent Source call derives sufficient fuel for the
accepted public handle checkpoint. The exact result and reached heap embed
without a stage outcome through the retained finite lexical body. -/
theorem source_has_sufficient_fuel {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        (Staging.Recursive.Lifting.embed outcome) after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨_callableEq, calleeTyped, _packedRelated, _packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  have runtime := anchor_runtime (anchor := anchor) bodyTyping
  obtain ⟨_parameters, _result, signatures, sourceCode, evidence, _captures⟩ := calleeTyped.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked recipe.compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
      sourceCode.requirement_ledger.idsUnique, evidence⟩
  have staged : Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages invocation
      anchor.function.context before entry.source sources (Staging.Recursive.Lifting.embed outcome) after := by
    rw [sourceEq] at trace ⊢
    exact GeneralizedLocalSourceApplicationLifting.selected_association_exact association frame selectedBodies
      (source_arguments functions bodyTyping history entry inHistory entryType sourceEq input started parameterView metadata packing arity) arity.symm trace
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace staged
  exact has_sufficient_fuel functions profile receiver extension bodyTyping selectedBodies history entry inHistory
    entryType sourceEq association owner atFrame input started parameterView metadata packing arity measured

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicMaterializedHandleMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicRetainedMaterializedHandle
/-! The actual accepted direct-handle checkpoint and current public history
supply input, heap and captured Source typing for a retained materialized row.
The row is recovered from the positively retained output certificate. No
caller supplies an association or a call meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicRetainedMaterializedHandle
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
  (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
    (Program.ofChecked recipe.compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys functions
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    completion.result.context.registry anchor session mapping world before store caller entries)
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

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping history inHistory entryType sourceEq in
/-- Current retained typing identifies the actual Source frame before the
independent call trace is constructed. No completed target call is needed. -/
theorem source_frame : Dynamic.ClosureFrame (Program.ofChecked recipe.compiled.sourceProgram) function := by
  obtain ⟨_imported, _represented, typed⟩ := history.current.2.2.2.2 entry inHistory
  rw [entryType, sourceEq] at typed
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  obtain ⟨_parameters, _result, signatures, sourceCode, evidence, _captures⟩ := typed.closure_function_inv
  exact ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
    sourceCode.requirement_ledger.idsUnique, evidence⟩

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq retained input started parameterView metadata in
/-- Finite completion of the original public checkpoint reconstructs the
materialized Source call using its current captures and packed input. -/
theorem completed_reflects {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore) (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
          anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwareSelectedPublicMaterializedHandleMeaning.completed_reflects functions profile receiver extension
    bodyTyping selectedBodies history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata completed invocation

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq retained input started parameterView metadata in
/-- A finite independent Source call supplies sufficient fuel for the same
accepted public checkpoint, including its exact failure store. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
      anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwareSelectedPublicMaterializedHandleMeaning.has_sufficient_fuel functions profile receiver extension
    bodyTyping selectedBodies history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata packing arity trace

include profile receiver extension bodyTyping selectedBodies history inHistory entryType sourceEq retained input started parameterView metadata in
/-- An ordinary independent Source call derives sufficient fuel for the
accepted public handle checkpoint. The exact result and reached heap embed
without a stage outcome through the retained finite lexical body. -/
theorem source_has_sufficient_fuel {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        (Staging.Recursive.Lifting.embed outcome) after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwareSelectedPublicMaterializedHandleMeaning.source_has_sufficient_fuel (invocation := invocation) functions profile receiver extension
    bodyTyping selectedBodies history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata packing arity trace

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicRetainedMaterializedHandle
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryRegistryExtension
/-! A real input encoder may extend the current metadata table. The entire
history moves to that table without changing its session, heap, captures or
ordered entries. No metadata can be recovered from a larger unrelated table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryRegistryExtension
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CellAwarePublicFunctionHistory (History Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry IssuedEntry)

private theorem outcome_extend
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {registry future : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Core.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome} {native : Core.Value}
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world sourceType type faults outcome native)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked future functions) mapping world sourceType type faults outcome native := by
  cases represented with
  | value related => exact .value (related.extend extension (.refl _) (.refl _))
  | fault related => exact .fault related

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  {registry future : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}

private theorem named_result (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world}
    {arguments : List Core.Value} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {native : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {faults : RecursiveStageMeaning.FaultRep}
    (result : Result (cells := cells registry) (functions := functions) (receiving := registry) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    Result (cells := cells future) (functions := functions) (receiving := future) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, outcome_extend result.2.1 extension,
    result.2.2.1.includes (covariant extension), result.2.2.2⟩

private theorem packed_result (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {native : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {faults : RecursiveStageMeaning.FaultRep}
    (result : CellAwarePublicApplicationResult.ResultAt (registry := registry) functions (cells registry) caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    CellAwarePublicApplicationResult.ResultAt (registry := future) functions (cells future) caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults :=
  ⟨outcome_extend result.1 extension,
    result.2.1.includes (covariant extension), result.2.2⟩

private theorem issued_entry {artifact : Artifact} {before after : Session artifact} {entry : Entry}
    (receipt : IssuedEntry headers keys functions registry anchor before after entry) :
    IssuedEntry headers keys functions future anchor before after entry := by
  cases receipt with
  | named prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      exact .named prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded wellFormed
  | builtin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      exact .builtin prepared headers keys bodyRegistry future faults profile anchor issuance atRecipe handleValue encoded
  | physicalNamed prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      exact .physicalNamed prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded wellFormed
  | physicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      exact .physicalNamedSelected prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded certified
  | physicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      exact .physicalBuiltin prepared headers keys bodyRegistry future faults profile anchor issuance atRecipe handleValue encoded
  | preparedPhysicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      exact .preparedPhysicalNamedSelected prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded certified
  | preparedPhysicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      exact .preparedPhysicalBuiltin prepared headers keys bodyRegistry future faults profile anchor issuance atRecipe handleValue encoded

/-- Only a forward extension of the actual metadata table is used. Every
historical result, including a failed call, keeps its original state and order. -/
theorem extend_history (covariant : CellAwarePublicCells.ExtendsRegistry cells) {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    History headers keys functions (cells future) future anchor session mapping world heap store caller entries := by
  induction history with
  | first sameCompiled started selected succeeded result reached post addition =>
      exact .first sameCompiled started selected succeeded (named_result covariant result extension) reached post addition
  | next prior sameCompiled started selected succeeded result reached post addition ih =>
      exact .next ih sameCompiled started selected succeeded (named_result covariant result extension) reached post addition
  | first_export_error sameCompiled started selected exported result reached post =>
      exact .first_export_error sameCompiled started selected exported (named_result covariant result extension) reached post
  | next_export_error prior sameCompiled started selected exported result reached post ih =>
      exact .next_export_error ih sameCompiled started selected exported (named_result covariant result extension) reached post
  | first_failed sameCompiled started selected failed result reached post heapTyped =>
      exact .first_failed sameCompiled started selected failed (named_result covariant result extension) reached post heapTyped
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      exact .failed ih sameCompiled started selected failed (named_result covariant result extension) reached post heapTyped
  | packed_next prior started succeeded result reached post addition ih =>
      exact .packed_next ih started succeeded (packed_result covariant result extension) reached post addition
  | packed_failed prior started failed result reached post heapTyped ih =>
      exact .packed_failed ih started failed (packed_result covariant result extension) reached post heapTyped
  | packed_export_error prior started exported result reached post ih =>
      exact .packed_export_error ih started exported (packed_result covariant result extension) reached post
  | issued prior continued ih => exact .issued ih continued
  | remember_issued prior receipt ih => exact .remember_issued ih (issued_entry receipt)
  | restored prior restored ih => exact .restored ih restored

/-- A history retains the genuine entry selected by its first named startup,
including when that call failed or later handles were restored. -/
theorem indexed_entry {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries) :
    ∃ entry, entry ∈ compiled.indexed.entries := by
  induction history with
  | first _ _ selected _ _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | first_export_error _ _ selected _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | next_export_error _ _ _ _ _ _ _ _ ih => exact ih
  | first_failed _ _ selected _ _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | next _ _ _ _ _ _ _ _ _ ih => exact ih
  | failed _ _ _ _ _ _ _ _ _ ih => exact ih
  | packed_next _ _ _ _ _ _ _ ih => exact ih
  | packed_failed _ _ _ _ _ _ _ ih => exact ih
  | packed_export_error _ _ _ _ _ _ ih => exact ih
  | issued _ _ ih => exact ih
  | remember_issued _ _ ih => exact ih
  | restored _ _ ih => exact ih

/-- The first actual root fixes a retained named header even if its result
contains no function handle. Later session transitions preserve that origin. -/
theorem named_header {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries) :
    ∃ header, header ∈ headers := by
  induction history with
  | first _ _ selected _ _ _ _ _ => exact ⟨_, selected.1⟩
  | first_export_error _ _ selected _ _ _ _ => exact ⟨_, selected.1⟩
  | next_export_error _ _ _ _ _ _ _ _ ih => exact ih
  | first_failed _ _ selected _ _ _ _ _ => exact ⟨_, selected.1⟩
  | next _ _ _ _ _ _ _ _ _ ih => exact ih
  | failed _ _ _ _ _ _ _ _ _ ih => exact ih
  | packed_next _ _ _ _ _ _ _ ih => exact ih
  | packed_failed _ _ _ _ _ _ _ ih => exact ih
  | packed_export_error _ _ _ _ _ _ ih => exact ih
  | issued _ _ ih => exact ih
  | remember_issued _ _ ih => exact ih
  | restored _ _ ih => exact ih

/-- The retained named row gives the genuine compiler diagnostic inventory.
No fallback entry or unrelated native execution is used. -/
theorem diagnostics_present {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries) :
    ∃ program, compiled.indexed.base.diagnostics = some program := by
  obtain ⟨header, _⟩ := named_header history
  obtain ⟨diagnostics, _, actual, _⟩ := NamedCalls.compiled_at compiled.indexed header.selected
  exact ⟨diagnostics, actual⟩

/-- The original accepted packed encoder supplies the extension. This keeps
history at the exact table used to decode this call's eventual public result. -/
theorem at_packed_start (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions (cells encodedValues.registry) encodedValues.registry anchor session mapping world heap store caller entries := by
  obtain ⟨before, encoded, actualRegistry, _owner, _accepted, _value, sameRegistry⟩ := started.raw
  have same : before = registry := actualRegistry.symm.trans atRegistry
  have extended : SourceCoreRawMetadata.Extends registry encodedValues.registry := by
    rw [← same, ← sameRegistry]
    exact encoded.preserves
  exact ⟨extended, extend_history covariant history extended⟩

/-- Named startup extends the same history using the complete actual ordered
input vector, including values that introduce constructor or mapping metadata. -/
theorem at_named_start (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} {root : Root recipe.compiled}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    {inputFuel : Nat} {checkpoint : Checkpoint artifact} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key arguments inputFuel
      checkpoint recipe root world store native encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions (cells encodedValues.registry) encodedValues.registry anchor session mapping world heap store caller entries := by
  have extended := started.original.metadata_extension atRegistry
  have actual := started.values
  cases checkpoint
  change _ = encodedValues at actual
  dsimp only at extended
  rw [actual] at extended
  exact ⟨extended, extend_history covariant history extended⟩


/-- Current handle identity and the actual packed encoder derive input meaning
in the very table used by public output decoding. Heap and capture meaning
come from the retained history, with no receiving-registry assumption. -/
theorem at_packed_input (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} (sameCompiled : recipe.compiled = compiled)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session entry.handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions (cells encodedValues.registry) encodedValues.registry anchor session mapping world heap store caller entries ∧
    ValueRep compiled.compatible.checked encodedValues.registry functions mapping world
      sourceParameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source sourceParameter := by
  cases sameCompiled
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨extended, current⟩ := at_packed_start covariant history atRegistry started
  obtain ⟨represented, typed⟩ := CellAwarePublicPackedInputs.history_input_compatible started current input parameterView (.refl _)
  exact ⟨extended, current, represented, typed⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicHistoryRegistryExtension
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicActualRegistryStart
/-! The actual packed startup determines the receiving context. Current
history supplies both the retained callable and every nested input handle;
the encoder supplies the forward registry extension. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicActualRegistryStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPublicFaultReceivers

variable {recipe : Recipe}
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}

/-- Construct the actual receiver and input meaning together. No completed
native execution, future registry or reverse extension is supplied. -/
theorem packed_input (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session entry.handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry ∈ recipe.compiled.indexed.entries ∧
      receiver.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiver.entry
        receiver.result.context.registry receiver.result.extension receiver.result.diagnostics ∧
      SourceCoreRawMetadata.Extends registry receiver.result.context.registry ∧
      History headers keys functions (cells receiver.result.context.registry) receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ValueRep recipe.compiled.compatible.checked receiver.result.context.registry functions mapping world
        sourceParameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source sourceParameter ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained, represented, typed⟩ :=
    CellAwarePublicHistoryRegistryExtension.at_packed_input covariant rfl member entryType input history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := CellAwarePublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := CellAwarePublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_, ?_, typed,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained
  · rw [contextAt]; exact represented

/-- Named input encoding chooses the receiver and transports the entire
retained history along its actual forward metadata extension. -/
theorem named_start (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (history : History headers keys functions (cells registry) registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    {root : Root recipe.compiled} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key arguments inputFuel
      checkpoint recipe root world store native encodedValues) :
    ∃ receiver : Receiver recipe.compiled.indexed,
      receiver.entry ∈ recipe.compiled.indexed.entries ∧
      receiver.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiver.entry
        receiver.result.context.registry receiver.result.extension receiver.result.diagnostics ∧
      SourceCoreRawMetadata.Extends registry receiver.result.context.registry ∧
      History headers keys functions (cells receiver.result.context.registry) receiver.result.context.registry anchor
        session mapping world heap store caller entries ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiver.result.diagnostics.diagnostic? token) := by
  obtain ⟨extended, retained⟩ :=
    CellAwarePublicHistoryRegistryExtension.at_named_start covariant history atRegistry started
  obtain ⟨indexed, indexedMember⟩ := CellAwarePublicHistoryRegistryExtension.indexed_entry history
  obtain ⟨receiver, indexedAt, contextAt, issued⟩ :=
    Receiver.at_context recipe.compiled indexed encodedValues started.owner
  obtain ⟨program, present⟩ := CellAwarePublicHistoryRegistryExtension.diagnostics_present history
  refine ⟨receiver, indexedAt ▸ indexedMember, contextAt, issued, ?_, ?_,
    fun token => RecursiveNamedPublicCheckpointReceiver.diagnostic_eq
      started.recipe_eq started.values contextAt issued present token⟩
  · rw [contextAt]; exact extended
  · rw [contextAt]; exact retained

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicActualRegistryStart
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleMeaning
/-! Actual history and input encoding supply direct callable arguments.
The retained builtin keeps its genuine compiler identity. Source and host raw
signatures remain distinct, and the complete returned caller is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (Entry)
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open CellAwarePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {bodyFaults : FunctionCalls.FaultRep}
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  (cells : GenericHeap.CellModel recipe.compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile) cells
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : BuiltinFunctionId} (sourceEq : entry.source = .builtin ⟨function⟩)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "functions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include history member entryType input started parameterView metadata in
private theorem current_inputs :
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      (.function parameter result) entry.source callable
      (CallableContract.functionType nativeParameter nativeResult) ∧
    Dynamic.ValueHasType anchor.function.context before entry.source (.function parameter result) ∧
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      parameter packedSource packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context before packedSource parameter := by
  obtain ⟨imported, represented, typed⟩ := history.current.2.2.2.2 entry member
  have callableEq := started.callable_eq imported
  rw [entryType] at represented typed
  rw [← callableEq] at represented
  have nativeTypeEq : entry.nativeType = CallableContract.functionType nativeParameter nativeResult :=
    represented.runtime_hasType.type_eq.symm.trans started.callableTyped.type_eq
  rw [nativeTypeEq] at represented
  obtain ⟨packedRelated, packedTyped⟩ := CellAwarePublicPackedInputs.history_input_compatible started history input parameterView.symm metadata
  exact ⟨represented, typed, packedRelated, packedTyped⟩

include profile cells history entry member entryType sourceEq input started parameterView metadata in
/-- Actual current history and packed encoding close the direct native result
against independent Source execution, including the ordered Source arguments. -/
theorem completed_reflects_at_arity
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
          invocation anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs profile cells history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  rw [sourceEq] at calleeRelated calleeTyped ⊢
  exact CellAwareBuiltinPackedApplication.reflects_packed_at_arity profile cells caller stable
    heapTyped calleeTyped calleeRelated heaps packedRelated (invocation := invocation) measured

include profile cells history entry member entryType sourceEq input started parameterView metadata in
theorem completed_reflects
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
          invocation anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := completed_reflects_at_arity profile cells history entry member entryType sourceEq input
    started parameterView metadata completed invocation
  exact ⟨sources, packing, meaning⟩

include profile cells history entry member entryType sourceEq input started parameterView metadata in
/-- The actual callable, encoded input and genuine Source arity derive native
completion for every sufficient fuel, including effects before a Source fault. -/
theorem has_sufficient_fuel_at_arity {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs profile cells history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  rw [sourceEq] at calleeRelated calleeTyped arity trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    CellAwareBuiltinPackedApplication.preserves_packed profile cells caller stable
      heapTyped calleeTyped calleeRelated heaps packedRelated
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

include profile cells history entry member entryType sourceEq input started parameterView metadata in
/-- Source success supplies the arity without an additional boundary receipt. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact has_sufficient_fuel_at_arity profile cells history entry member entryType sourceEq input started parameterView metadata
    packing (.of_value trace) trace

include profile cells history entry member entryType sourceEq input started parameterView metadata in
/-- Independent ordinary Source success derives sufficient execution fuel for
this exact accepted public builtin call, with the same mixed heap. -/
theorem source_has_sufficient_fuel {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  have staged : Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages invocation
      anchor.function.context before entry.source sources (.value sourceResult) after := by
    rw [sourceEq] at trace ⊢
    exact SelectedCompilationStageLiftBuiltin.builtin_application trace.sound
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace staged
  exact has_sufficient_fuel profile cells history entry member entryType sourceEq input started parameterView metadata packing measured

end Meaning
end Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleForward
/-! Actual history and input encoding supply direct callable arguments.
The retained builtin keeps its genuine compiler identity. Source and host raw
signatures remain distinct, and the complete returned caller is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleForward
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (Entry)
open CellAwarePublicFunctionHistory (History Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open CellAwarePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {bodyFaults : FunctionCalls.FaultRep}
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  (cells : GenericHeap.CellModel recipe.compiled.indexed.layouts.definitions)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile) cells
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : BuiltinFunctionId} (sourceEq : entry.source = .builtin ⟨function⟩)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "functionModel" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry bodyFaults profile
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store)
  (exactRegistry : completion.result.context.registry = encodedValues.registry)
  (resultView : SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)

include profile cells history member entryType sourceEq input started parameterView metadata
  physical exactRegistry resultView ready atCheckpoint in
/-- Independent ordinary Source execution of a genuinely exported builtin
supplies enough fuel for public success and preserves the complete prior history. -/
theorem source_success {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {value : Dynamic.Value} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources (.value value) after) :
    ∃ native finalStore finalMap finalWorld requiredExecution requiredOutput,
      ResultAt (registry := completion.result.context.registry) functionModel cells caller anchor.function.context result nativeResult
        (.value value) after native finalStore finalMap finalWorld callFaults ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded returned ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          returned.IndexedAt actual ∧ CallableIndexedOwnedFunctionState.Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functionModel) (cells := cells)
            (receiving := completion.result.context.registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt completion.result.context.registry ∧ actual.session.ExportsReady := by
  obtain ⟨native, finalStore, finalMap, finalWorld, requiredExecution, runs, semantic⟩ :=
    CellAwarePublicBuiltinHandleMeaning.source_has_sufficient_fuel (invocation := invocation)
      profile cells history entry member entryType sourceEq
      input started parameterView metadata packing trace
  obtain ⟨requiredOutput, exported⟩ := CellAwarePublicDirectOutput.after_success functionModel cells started
    exactRegistry resultView ready atCheckpoint semantic runs ⟨history, physical⟩
  exact ⟨native, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput, semantic, exported⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.CellAwarePublicBuiltinHandleForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicClosureHistory
/-! Public history is instantiated directly with positive physical closure
origins. Original export and reimport receipts preserve those origins through
containers, repeated handles, and actual returned sessions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicClosureHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open RecursiveNamedPublicFunctionHistory (Caller Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry receiving : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}

local notation "rootFunctions" => CellAwarePhysicalFunctionOrigins.functions headers keys bodyRegistry faults profile

abbrev History {artifact : Artifact} (session : Session artifact)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store)
    (caller : Caller headers keys mapping world heap store) (entries : List Entry) : Prop :=
  CellAwarePublicPhysicalHistory.History (functions := rootFunctions) (cells := cells) (receiving := receiving) (anchor := anchor)
    session mapping world heap store caller entries

/-- The original history supplies positive captured members, the current heap,
and the exact physical cache. The actual input encoder chooses each retained
handle at its original argument position. -/
theorem History.current_arguments
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
    {caller : Caller headers keys mapping world before store}
    (history : History (cells := cells) (bodyRegistry := bodyRegistry) (faults := faults) (profile := profile)
      (receiving := receiving) (anchor := anchor) session mapping world before store caller entries)
    {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
    {root : Root compiled} {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers root header)
    {checkpoint : Checkpoint artifact} {key : SourceCoreIndexedSession.Key}
    {publicArguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {payloads : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root) world store payloads encodedValues)
    {arguments : List Dynamic.Value}
    (inputReceipts : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled) :
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      GenericHeap.CellHeapRepresents cells mapping world before store ∧
      Dynamic.HeapWellTyped header.function.context before ∧
      CallableIndexedParameterMeaning.Arguments
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving rootFunctions)
        mapping world header.bindings arguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context before arguments header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨_nativeAt, heaps, stable, heapTyped, retained⟩ := history.semantic.current
  have contexts := SelectedCompilationPublicReturnedValues.header_context_supports anchor header bodyTyping
  obtain ⟨represented, argumentsTyped⟩ :=
    SelectedCompilationPublicHistoryArgumentsReceiving.StartAt.history_arguments_receiving
      started _ selected entries (fun entry member => (retained entry member).1)
      (fun entry member => (retained entry member).2.1)
      (fun entry member => (retained entry member).2.2.transportContext contexts.1)
      inputReceipts metadata (SelectedCompilationHeaderCertificates.certified bodyTyping header)
  exact ⟨stable, heaps, heapTyped.transportContext contexts.1, represented, argumentsTyped⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicClosureHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput
/-! A direct handle call retains its actual mixed heap and prior public history.
The original requested signature and output codec determine public completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header)
open CellAwarePublicFunctionHistory (Caller)
open CellAwarePublicApplicationResult (ResultAt)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  {parameter requested sourceResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value}
  (started : StartAt session handle argument inputFuel checkpoint recipe world store
    parameter requested nativeParameter nativeResult callable packed encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : ResultAt (registry := registry) functions cells caller anchor.function.context sourceResult nativeResult
    outcome after native finalStore finalMap finalWorld faults)

variable {proofFuel executionFuel outputFuel : Nat}
  (completed : checkpoint.NativeDone proofFuel native finalStore)
  {completion : SourceCoreExecution.Completion publicArtifact}
  (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded completion))

include atCheckpoint completed resumed in
/-- Native determinism identifies the Source-derived value and heap with the
actual observed public completion, regardless of the proof's fuel budget. -/
theorem actual_result :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual := by
  obtain ⟨actual, generation, observed, observedStore, done, exported, atReturned⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨_leftSteps, _leftEnough, left⟩ := runStateful_sound completed
  obtain ⟨_rightSteps, _rightEnough, right⟩ := runStateful_sound done
  obtain ⟨_steps, sameValue, sameStore⟩ := left.final_unique right
  cases sameValue
  cases sameStore
  exact ⟨actual, generation, exported, atReturned⟩

include started exactRegistry ready atCheckpoint result completed resumed in
theorem after_success {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
        (receiving := registry) (anchor := anchor)
        actual.session finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨actual, generation, exported, atReturned⟩ := actual_result atCheckpoint completed resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_packed_success started.original exported result
  exact ⟨actual, generation, reached, exported, atReturned, related,
    ⟨retained, history.physical.extend result.2.2.2.2.1⟩,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicDirectObservedOutput
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailure
/-! Actual fault results determine the public failed session and preserve its
reached mixed heap, physical cache and retained function history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwarePublicFunctionHistory (Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world before store}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {root : Root recipe.compiled}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
    recipe root world store arguments encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {failure : Staging.Recursive.Failure} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (heapTyped : Dynamic.HeapWellTyped anchor.function.context after)
  (result : Result (cells := cells) (functions := functions) (receiving := registry) (anchor := anchor)
    owner caller header capture arguments (.fault failure) after native finalStore finalMap finalWorld faults)
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)


include started exactRegistry ready atCheckpoint result completes in
theorem failed :
    ∃ token, faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ actual.RegistryAt registry ∧ actual.ExportsReady := by
  obtain ⟨token, nativeEq, represented⟩ : ∃ token,
      native = .inLeft header.output (.word token) ∧ faults failure token := by
    have related := result.2.1
    cases related with
    | fault represented => exact ⟨_, rfl, represented⟩
  have checkpointReady := started.original.initial_registry.exportsReady ready
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  have completed := completes executionFuel enough
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed (by rw [nativeEq]; rfl)
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failedAt, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  have returnedRegistry : actual.RegistryAt registry := by
    rw [exactRegistry]
    exact congrArg SourceCoreCompatibleValues.Context.registry (failedAt.2.2.2.2.1.trans started.values)
  exact ⟨returned, actual, outcomeEq, failedAt, returnedAt, returnedRegistry, failedAt.exportsReady checkpointReady⟩

include selected started exactRegistry ready atCheckpoint heapTyped result completes in
theorem first_failure
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ token, faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached [] ∧
          actual.RegistryAt registry ∧ returned.ExportsReady := by
  obtain ⟨token, represented, output⟩ :=
    failed functions cells started exactRegistry ready atCheckpoint result completes
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, failedOutcome, actualResult, actualAt, registryAt, actualReady⟩ :=
    output executionFuel outputFuel outcome enough resumed
  obtain ⟨reached, related, history⟩ := CellAwarePublicFunctionHistory.first_failure
    rfl started selected actualResult result heapTyped
  exact ⟨returned, actual, reached, failedOutcome, actualResult, actualAt, related,
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩,
    registryAt, actualAt.exportsReady_iff.mpr actualReady⟩

include selected started exactRegistry ready atCheckpoint heapTyped result completes in
theorem after_failure {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ token, faults failure token ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (returned : SourceCoreExecution.Session publicArtifact) (actual : Session artifact)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .failed token returned ∧
          checkpoint.FailedResultAt executionFuel native finalStore token actual ∧
          returned.IndexedAt actual ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual finalMap finalWorld after finalStore reached entries ∧
          actual.RegistryAt registry ∧ returned.ExportsReady := by
  obtain ⟨token, represented, output⟩ :=
    failed functions cells started exactRegistry ready atCheckpoint result completes
  refine ⟨token, represented, ?_⟩
  intro executionFuel outputFuel outcome enough resumed
  obtain ⟨returned, actual, failedOutcome, actualResult, actualAt, registryAt, actualReady⟩ :=
    output executionFuel outputFuel outcome enough resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_failure
    rfl started selected actualResult result heapTyped
  exact ⟨returned, actual, reached, failedOutcome, actualResult, actualAt, related,
    history.after_result result retained, registryAt, actualAt.exportsReady_iff.mpr actualReady⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedFailure
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionState
/-! An actual public session carries its indexed runtime, Source heap and
positive physical history. Calls retain their own public options and receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)}

structure State (rows : Inventory inputs)
    (functions : CompatiblePayload.FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (cells : SourceCoreRawMetadata.Registry →
      GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (recipe : SourceCoreIndexedSession.Recipe)
    {publicArtifact : SourceCoreExecution.Artifact}
    (publicSession : SourceCoreExecution.Session publicArtifact) (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers rows)
    (keys compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : CellAwarePublicPhysicalHistory.History (headers := headers rows)
    (keys := keys compiled) (functions := functions)
    (cells := cells receiving.result.context.registry)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    session mapping world heap store caller entries

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionRegistry
/-! The actual input encoder selects the receiving metadata table. Historical
Source results and physical cache authority move together to that table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {functions : CompatiblePayload.FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.at_named_request (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows functions cells anchor initial recipe session entries)
    {checkpoint : SourceCoreExecution.Checkpoint artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {inputFuel : Nat}
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      checkpoint state.session key publicArguments inputFuel state.world state.store) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = request.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry ∧
      CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys compiled)
        (functions := functions) (cells := cells receiving.result.context.registry) (receiving := receiving.result.context.registry)
        (anchor := anchor) state.session state.mapping state.world state.heap state.store state.caller entries := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, _diagnostic⟩ :=
    CellAwarePublicActualRegistryStart.named_start covariant state.history.semantic state.registry request.started
  exact ⟨receiving, contextAt, issued, state.extension.trans extended, retained, state.history.physical⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicSessionState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicHandleStart
/-! A direct packed handle start is recovered from the actual public receipt.
Its current history and encoder supply the receiving registry and input meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicHandleStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

structure StartedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (handle : SourceCorePublicValues.Handle)
    (argument : SourceCorePublicValues.Value) (fuel : Nat) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  accepted : session.startHandlePacked handle argument fuel = .ok checkpoint

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}
  (state : CellAwarePublicSessionState.State rows functions cells anchor initial recipe session entries)
  (entry : Entry) {parameter result : TypeSystem.Ty}
  {argument : SourceCorePublicValues.Value} {fuel : Nat}
  (call : StartedCall session entry.handle argument fuel)

structure Started (parameter result : TypeSystem.Ty) where
  checkpoint : SourceCoreIndexedSession.Checkpoint state.artifact
  actualParameter : TypeSystem.Ty
  actualResult : TypeSystem.Ty
  nativeParameter : Core.Ty
  nativeResult : Core.Ty
  callable : Core.Value
  packed : Core.Value
  encodedValues : SourceCoreCompatibleValues.Context
  atCheckpoint : call.checkpoint.IndexedAt checkpoint
  started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt state.session entry.handle argument fuel
    checkpoint recipe state.world state.store actualParameter actualResult nativeParameter nativeResult callable packed encodedValues
  parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter
  resultView : SourceCoreRawMetadata.runtimeType result = SourceCoreRawMetadata.runtimeType actualResult

/-- This inverts only the accepted original public start; it never executes a
second call or obtains callable meaning from the handle's spelling. -/
theorem from_call (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result) :
    Nonempty (Started state entry call parameter result) := by
  obtain ⟨checkpoint,atCheckpoint,original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession call.accepted
  have imported := (state.history.semantic.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter,actualResult,nativeParameter,nativeResult,callable,packed,encodedValues,
      started,parameterView,resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.semantic.current.1 imported original
  exact ⟨⟨checkpoint,actualParameter,actualResult,nativeParameter,nativeResult,callable,packed,encodedValues,
    atCheckpoint,started,parameterView.symm,resultView.symm⟩⟩

structure Ready (start : Started state entry call parameter result) (source : Dynamic.Value) where
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  contextAt : receiving.result.context = start.encodedValues
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  history : CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys recipe.compiled)
    (functions := functions) (cells := cells receiving.result.context.registry)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    state.session state.mapping state.world state.heap state.store state.caller entries
  represented : ValueRep recipe.compiled.compatible.checked receiving.result.context.registry functions
    state.mapping state.world parameter source start.packed start.nativeParameter
  typed : Dynamic.ValueHasType anchor.function.context state.heap source parameter

/-- The original packed encoder transports all retained functions and derives
the Source input type at the exact current heap. -/
theorem of_started (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (member : entry ∈ entries) (entryType : entry.sourceType = .function parameter result)
    {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument source)
    (start : Started state entry call parameter result) :
    Nonempty (Ready state entry call start source) := by
  obtain ⟨receiving,_indexed,contextAt,issued,extended,retained,represented,typed,_diagnostics⟩ :=
    CellAwarePublicActualRegistryStart.packed_input covariant state.history.semantic state.registry
      member entryType input start.started
  exact ⟨⟨receiving,contextAt,issued,state.extension.trans extended,
    ⟨retained,state.history.physical⟩,represented,typed⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicHandleStart
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialArguments
/-! Actual bootstrap and original public data encoding construct the positive
closure model and every installed cache cell, including selected method closures. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
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
  (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
    header.function.context publicArguments header.types)
  (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CellAwarePhysicalFunctionOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include distinct bodyTyping prepared selected opened fresh ready sameRuntime atSession started inputTypes inputMeanings metadata in
/-- This proof is consumed immediately by the public endpoints below. The
runtime-preservation receipt fixes the initial store/world; the argument producer uses
the caller's receiving metadata without identifying two registries. -/
theorem initial_data_arguments :
    ∃ caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol rootHeaders rootKeys 0).State
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val ∧
      (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
        some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
          ((rootOwner).key.locations header)) ∧
      GenericHeap.CellHeapRepresents
        (CellAwarePublicCells.generalized rootFunctions
          (GeneralizedLocalInstanceValues.model compiled.indexed) completion.result.context.registry)
        [] world ⟨[]⟩ store ∧
      Dynamic.HeapWellTyped header.function.context ⟨[]⟩ ∧
      CallableIndexedParameterMeaning.Arguments rootModel [] world header.bindings arguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types := by
  obtain ⟨caller, stable, globals, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := completion)
      (profile := profile) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (bodyTyping := bodyTyping) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := sameRuntime)
      (atSession := atSession) (started := started) (inputTypes := inputTypes)
      (inputMeanings := inputMeanings) (metadata := metadata)
  refine ⟨caller, stable, globals,
    CellAwarePublicCells.generalized_initial (GeneralizedLocalInstanceValues.model compiled.indexed)
      (CompatibleAmbientHeap.extend_definitions (CellAwarePhysicalFunctionOrigins.includes_prepared profile) (.refl _) heaps),
    heapTyped, ?_, argumentsTyped⟩
  clear started inputMeanings argumentsTyped
  generalize header.bindings = bindings at represented ⊢
  induction represented with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons (CompatiblePayload.ValueRep.map_functions
      (CellAwarePhysicalFunctionOrigins.includes_prepared profile) head) ih

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialArguments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
/-! The actual bootstrap and public input encoding produce the initial mixed
heap, caller, diagnostic receiver and parameter representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall)
open SelectedCompilationPublicSessionInitial (Started)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} {call : StartedCall session key publicArguments options}

/-- Actual public compilation and startup recover the same recipe and selected
root before any Source execution premise is introduced. -/
theorem from_call
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (opened : artifact.CompiledAt publicCompiled)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (selectRoot : ∀ root ∈ recipe.roots, RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header) :
    Nonempty (Started rows prepared header call) := by
  obtain ⟨actualRecipe, nativeArtifact, nativeSession, checkpoint, root, world, store, native,
      encodedValues, atArtifact, _prepared, _source, atSession, atCheckpoint, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start compiled opened call.started
  have same : actualRecipe = recipe := by
    have actual := atArtifact.compiled_recipe
    cases publicCompiled
    exact Option.some.inj (actual.symm.trans selected)
  cases same
  exact ⟨{
    publicCompiled := publicCompiled, artifact := nativeArtifact, nativeSession := nativeSession,
    checkpoint := checkpoint, root := root, world := world, store := store, native := native,
    encodedValues := encodedValues, opened := atArtifact, atSession := atSession,
    atCheckpoint := atCheckpoint, started := started,
    selected := selectRoot root (List.mem_of_find?_eq_some started.selected),
    bootstrap := bootstrap, bootstrapFuel := bootstrapFuel, fresh := fresh,
    authority := authority, ready := ready }⟩

/-- A selected factory row supplies the receiver entry; the actual encoder
supplies its metadata. No body meaning or pre-existing receiver is required. -/
theorem receiver (start : Started rows prepared header call) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed,
      receiving.result.context = start.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry
        receiving.result.context.registry := by
  obtain ⟨entry, _member, _shape, _found⟩ := start.selected.2
  obtain ⟨receiving, _entry, contextAt, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_context recipe.compiled entry
      start.encodedValues start.started.owner
  exact ⟨receiving, contextAt, issued, receiving.result.extension⟩

structure Ready
    (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (start : Started rows prepared header call) (arguments : List Dynamic.Value) where
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  contextAt : receiving.result.context = start.encodedValues
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry
    receiving.result.context.registry
  exportsReady : start.nativeSession.ExportsReady
  caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol (headers rows) (keys recipe.compiled) 0).State
    ⟨[], [], start.world, ⟨[]⟩, start.store,
      SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed⟩
  stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val
  globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      ((owner recipe.compiled).key.locations header))
  keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical (owner recipe.compiled).key (headers rows)
  heaps : GenericHeap.CellHeapRepresents
    (CellAwarePublicCells.generalized
      (CellAwarePhysicalFunctionOrigins.functions (headers rows) (keys recipe.compiled) bodyRegistry semanticFaults profile)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed) receiving.result.context.registry)
    [] start.world ⟨[]⟩ start.store
  heapTyped : Dynamic.HeapWellTyped header.function.context ⟨[]⟩
  represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked receiving.result.context.registry
      (CellAwarePhysicalFunctionOrigins.functions (headers rows) (keys recipe.compiled) bodyRegistry semanticFaults profile))
    [] start.world header.bindings arguments start.native
  argumentsTyped : Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types

/-- These are consequences of the public bootstrap/start receipts and independent
input meanings. The selected-body typing interface remains narrower than a whole
program execution theorem. -/
theorem of_started
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
    (bodyRegistry : SourceCoreRawMetadata.Registry) (semanticFaults : FunctionCalls.FaultRep)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (start : Started rows prepared header call)
    {arguments : List Dynamic.Value}
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    Nonempty (Ready profile bodyRegistry semanticFaults start arguments) := by
  obtain ⟨receiving, contextAt, issued, extension⟩ := receiver start
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    CellAwarePublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := receiving)
      (profile := profile) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (bodyTyping := bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session)
      (atSession := start.atSession) (started := start.started)
      (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  exact ⟨⟨receiving, contextAt, issued, extension,
    start.atSession.exportsReady_iff.mp (start.ready.exportsReady start.authority),
    caller, stable, globalReference,
    CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical recipe.compiled (headers rows),
    heaps, heapTyped, represented, argumentsTyped⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialStart
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialSelectedStart
/-! The actual bootstrap and public input encoding produce the initial mixed
heap, caller, diagnostic receiver and parameter representation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialSelectedStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall)
open SelectedCompilationPublicSessionInitial (Started)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} {call : StartedCall session key publicArguments options}

/-- Actual public compilation and startup recover the same recipe and selected
root before any Source execution premise is introduced. -/
theorem from_selected_call
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (opened : artifact.CompiledAt publicCompiled)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (selectRoot : ∀ root ∈ recipe.roots, root.key = key → RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header) :
    Nonempty (Started rows prepared header call) := by
  obtain ⟨actualRecipe, nativeArtifact, nativeSession, checkpoint, root, world, store, native,
      encodedValues, atArtifact, _prepared, _source, atSession, atCheckpoint, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start compiled opened call.started
  have same : actualRecipe = recipe := by
    have actual := atArtifact.compiled_recipe
    cases publicCompiled
    exact Option.some.inj (actual.symm.trans selected)
  cases same
  exact ⟨{
    publicCompiled := publicCompiled, artifact := nativeArtifact, nativeSession := nativeSession,
    checkpoint := checkpoint, root := root, world := world, store := store, native := native,
    encodedValues := encodedValues, opened := atArtifact, atSession := atSession,
    atCheckpoint := atCheckpoint, started := started,
    selected := selectRoot root (List.mem_of_find?_eq_some started.selected)
      (of_decide_eq_true (List.find?_some
        (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key))
        started.selected)),
    bootstrap := bootstrap, bootstrapFuel := bootstrapFuel, fresh := fresh,
    authority := authority, ready := ready }⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicInitialSelectedStart
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedFaultHeap
/-! The actual current public input and retained callee supply the deep heap
typing needed after a measured faulting materialized call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedFaultHeap
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
  (history : History headers keys functions
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    completion.result.context.registry anchor session mapping world before store caller entries)
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

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping wellFormed history inHistory entryType input started parameterView metadata in
theorem after_fault {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {size : Nat} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) stages size invocation
      anchor.function.context before entry.source sources (.fault failure) after) :
    Dynamic.HeapWellTyped anchor.function.context after := by
  have current := history.current
  have typed := (current.2.2.2.2 entry inHistory).2.2
  rw [entryType] at typed
  obtain ⟨_packedRelated, packedTyped⟩ := CellAwarePublicPackedInputs.history_input_compatible
    started history input parameterView.symm metadata
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  exact (Staging.Recursive.FaultPreservation.applies wellFormed runtime
    current.2.2.2.1 typed packing packedTyped trace).1

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedFaultHeap
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedHandleMeaning
/-! The actual accepted direct-handle checkpoint and current public history
supply input, heap and captured Source typing for a retained materialized row.
Only compiler provenance identifies the row; no call meaning is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedHandleMeaning
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
  (history : History headers keys functions
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (inHistory : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : Dynamic.Closure} (sourceEq : entry.source = .closure function)
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Core.Ty}
  (association : Association recipe.compiled mapping world function entry.native bindings parameterCore resultCore)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (atFrame : association.AtFrame owner.key.frameLocation)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping in
private theorem anchor_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
    anchor.function.context anchor.function.source := by
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  rw [anchor.frame.context, anchor.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

include history inHistory entryType sourceEq input started parameterView metadata in
private theorem current_inputs :
    callable = entry.native ∧
    Dynamic.ValueHasType anchor.function.context before (.closure function) (.function parameter result) ∧
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      parameter packedSource packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context before packedSource parameter := by
  obtain ⟨imported, _represented, typed⟩ := history.current.2.2.2.2 entry inHistory
  have callableEq := started.callable_eq imported
  rw [entryType, sourceEq] at typed
  obtain ⟨packedRelated, packedTyped⟩ := CellAwarePublicPackedInputs.history_input_compatible started history input parameterView.symm metadata
  exact ⟨callableEq, typed, packedRelated, packedTyped⟩

include bodyTyping history inHistory entryType sourceEq input started parameterView metadata in
/-- Current public history and the accepted packed input recover Source argument
and capture typing at the exact incoming heap. -/
theorem source_arguments {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources := by
  obtain ⟨_callableEq, calleeTyped, _packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨parameterEq, _resultEq, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
  have sourceTyped := packing.unpackTypes (parameterEq ▸ packedTyped) (by simpa only [List.length_map] using arity)
  exact CallableIndexedOwnedStoredClosureSourceArguments.at_arguments (anchor_runtime bodyTyping) calleeTyped
    history.current.2.2.2.1 sourceTyped packing parameterEq.symm arity

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- Finite completion of the original public checkpoint reconstructs the
materialized Source call using its current captures and packed input. -/
theorem completed_reflects {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore) (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
          anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨callableEq, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (association.runtime_hasType.type_eq.symm.trans (callableEq ▸ started.callableTyped.type_eq))
  obtain ⟨rfl, rfl⟩ := nativeTypes
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  rw [callableEq] at measured
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    CellAwareMaterializedPackedApplication.reflects functions profile receiver extension caller stable
      (anchor_runtime bodyTyping) (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) heapTyped association owner atFrame calleeTyped packedTyped packedRelated heaps measured
  exact ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld,
    by simpa only [sourceEq] using trace, resultAt⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- A finite independent Source call supplies sufficient fuel for the same
accepted public checkpoint, including its exact failure store. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
      anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨callableEq, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  have nativeTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    (association.runtime_hasType.type_eq.symm.trans (callableEq ▸ started.callableTyped.type_eq))
  obtain ⟨rfl, rfl⟩ := nativeTypes
  rw [sourceEq] at trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    CellAwareMaterializedPackedApplication.preserves functions profile receiver extension caller stable
      (anchor_runtime bodyTyping) (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed) heapTyped association owner atFrame calleeTyped packedTyped packedRelated heaps
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  rw [← callableEq] at evaluated
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq atFrame input started parameterView metadata in
/-- An ordinary independent Source call derives sufficient fuel for the
accepted public handle checkpoint. The exact result and reached heap embed
without a stage outcome through the retained finite lexical body. -/
theorem source_has_sufficient_fuel {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        (Staging.Recursive.Lifting.embed outcome) after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨_callableEq, calleeTyped, _packedRelated, _packedTyped⟩ :=
    current_inputs functions history entry inHistory entryType sourceEq input started parameterView metadata
  have runtime := anchor_runtime (anchor := anchor) bodyTyping
  obtain ⟨_parameters, _result, signatures, sourceCode, evidence, _captures⟩ := calleeTyped.closure_function_inv
  have frame : Dynamic.ClosureFrame (Program.ofChecked recipe.compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
      sourceCode.requirement_ledger.idsUnique, evidence⟩
  have staged : Staging.Recursive.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages invocation
      anchor.function.context before entry.source sources (Staging.Recursive.Lifting.embed outcome) after := by
    rw [sourceEq] at trace ⊢
    exact GeneralizedLocalSourceApplicationLifting.selected_association_exact association frame (Staging.Recursive.SelectedPreservation.SelectedBodies.of_program wellFormed)
      (source_arguments functions bodyTyping history entry inHistory entryType sourceEq input started parameterView metadata packing arity) arity.symm trace
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.Applies.of_trace staged
  exact has_sufficient_fuel functions profile receiver extension bodyTyping wellFormed history entry inHistory
    entryType sourceEq association owner atFrame input started parameterView metadata packing arity measured

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicMaterializedHandleMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedCollection
/-! Public output fuel and actual export receipts retain returned function
leaves for later calls, including functions nested in products. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedCollection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwarePublicFunctionHistory (Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world before store}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {root : Root recipe.compiled}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
    recipe root world store arguments encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {source : Dynamic.Value} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : Result (cells := cells) (functions := functions) (receiving := registry) (anchor := anchor)
    owner caller header capture arguments (.value source) after native finalStore finalMap finalWorld faults)
  {requiredExecution : Nat}
  (completes : ∀ executionFuel, requiredExecution ≤ executionFuel → checkpoint.NativeDone executionFuel native finalStore)


include selected started exactRegistry ready atCheckpoint result completes in
/-- The first real output export collects selected function leaves, including
leaves inside products, at the exact returned heap and public session. -/
theorem first_collected
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
          ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
            ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
              added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
              CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
                (receiving := registry) (anchor := anchor)
                actual.session finalMap finalWorld after finalStore reached added := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    CellAwarePublicNamedOutput.exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  refine ⟨completion, actual, generation, succeeded, actualResult, actualAt,
    exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady, ?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨reached, added, handles, related, history⟩ :=
    CellAwarePublicFunctionHistory.first_collected rfl started selected requested actualResult result selection
  exact ⟨reached, added, handles, related,
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩⟩

include selected started exactRegistry ready atCheckpoint result completes in
/-- Later public outputs append selected leaves to the complete prior history;
intervening named calls retain the same captured locations in the reached heap. -/
theorem after_collected {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ requiredOutput,
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (completion : SourceCoreExecution.Completion publicArtifact) (actual : Completion artifact)
          (generation : SourceCorePublicValues.ExportGeneration),
          outcome = .succeeded completion ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
          completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
          ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
            ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
              added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
              CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
                (receiving := registry) (anchor := anchor)
                actual.session finalMap finalWorld after finalStore reached (entries ++ added) := by
  obtain ⟨_payload, requiredOutput, _nativeEq, _represented, exported⟩ :=
    CellAwarePublicNamedOutput.exports functions cells selected started exactRegistry ready atCheckpoint result completes
  refine ⟨requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome enough outputEnough resumed
  obtain ⟨completion, actual, generation, succeeded, actualResult, actualAt, returnedReady⟩ :=
    exported executionFuel outputFuel outcome enough outputEnough resumed
  refine ⟨completion, actual, generation, succeeded, actualResult, actualAt,
    exactRegistry.symm ▸ started.returned_registry actualResult, returnedReady, ?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨reached, added, handles, related, retained⟩ :=
    history.semantic.collect_success rfl started selected requested actualResult result selection
  exact ⟨reached, added, handles, related, history.after_result result retained⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedCollection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput
/-! Actual public success consumes the independent Source-derived native result
without assuming a numerical fuel bound for that observed completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwarePublicFunctionHistory (Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world before store}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {root : Root recipe.compiled}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
    recipe root world store arguments encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {source : Dynamic.Value} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : Result (cells := cells) (functions := functions) (receiving := registry) (anchor := anchor)
    owner caller header capture arguments (.value source) after native finalStore finalMap finalWorld faults)

variable {proofFuel executionFuel outputFuel : Nat}
  (completed : checkpoint.NativeDone proofFuel native finalStore)
  {completion : SourceCoreExecution.Completion publicArtifact}
  (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded completion))

include atCheckpoint completed resumed in
/-- Different fuel budgets for the same checkpoint cannot change a completed
value or store. The export receipt belongs to the actual observed resume. -/
theorem actual_result :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual := by
  obtain ⟨actual, generation, observed, observedStore, done, exported, atReturned⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨_leftSteps, _leftEnough, left⟩ := runStateful_sound completed
  obtain ⟨_rightSteps, _rightEnough, right⟩ := runStateful_sound done
  obtain ⟨_steps, sameValue, sameStore⟩ := left.final_unique right
  cases sameValue
  cases sameStore
  exact ⟨actual, generation, exported, atReturned⟩

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- An observed first success retains the exact Source-derived heap and
physical history, even when the observer did not know its sufficient fuel. -/
theorem first_success
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
        (receiving := registry) (anchor := anchor)
        actual.session finalMap finalWorld after finalStore reached [] ∧
      actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨actual, generation, exported, atReturned⟩ := actual_result atCheckpoint completed resumed
  obtain ⟨reached, related, history⟩ :=
    CellAwarePublicFunctionHistory.first_success rfl started selected exported result
  exact ⟨actual, generation, reached, exported, atReturned, related,
    ⟨history, CellAwarePublicPhysicalHistory.physical_of_result physical result⟩,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready)⟩

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- An observed later success preserves every earlier function handle and its
captures at the Source-derived heap reached by this invocation. -/
theorem after_success {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ Relates caller reached ∧
      CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
        (receiving := registry) (anchor := anchor)
        actual.session finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt registry ∧ actual.session.ExportsReady := by
  obtain ⟨actual, generation, exported, atReturned⟩ := actual_result atCheckpoint completed resumed
  obtain ⟨reached, related, retained⟩ := history.semantic.after_success rfl started selected exported result
  exact ⟨actual, generation, reached, exported, atReturned, related,
    history.after_result result retained, exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedOutput
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedCollection
/-! Actual public success consumes the independent Source-derived native result
without assuming a numerical fuel bound for that observed completion. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedCollection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
open CellAwarePublicFunctionHistory (Caller Result)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : Recipe}
  {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  (functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {owner : OwnedKey keys} {caller : Caller headers keys mapping world before store}
  {capture : NamedCapture headers owner.key header mapping world} {arguments : List Core.Value}
  {root : Root recipe.compiled}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
  {artifact : Artifact} {session : Session artifact} {checkpoint : Checkpoint artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {inputFuel : Nat} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : RecursiveNamedPublicStartMeaning.StartAt session key publicArguments inputFuel checkpoint
    recipe root world store arguments encodedValues)
  (exactRegistry : registry = encodedValues.registry)
  (ready : session.ExportsReady)
  {publicArtifact : SourceCoreExecution.Artifact} {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
  {source : Dynamic.Value} {after : Dynamic.Heap} {native : Core.Value} {finalStore : Store}
  {finalMap : LocationMap} {finalWorld : StoreTyping} {faults : RecursiveStageMeaning.FaultRep}
  (result : Result (cells := cells) (functions := functions) (receiving := registry) (anchor := anchor)
    owner caller header capture arguments (.value source) after native finalStore finalMap finalWorld faults)

variable {proofFuel executionFuel outputFuel : Nat}
  (completed : checkpoint.NativeDone proofFuel native finalStore)
  {completion : SourceCoreExecution.Completion publicArtifact}
  (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded completion))

include result in
private theorem selected_addition
    {actual : Completion artifact} {generation : SourceCorePublicValues.ExportGeneration}
    (requested : checkpoint.ResultTypeAt header.function.resultType)
    (exported : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual)
    (selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value) :
    ∃ (payload : Core.Value) (added : List Entry),
      native = .inRight .word payload ∧
      RecursiveNamedPublicOutputSelections.Selected selection source payload header.output outputFuel added ∧
      added.map Entry.handle = selection.handles ∧
      RecursiveNamedPublicFunctionHistory.Addition (checked := recipe.compiled.compatible.checked)
        checkpoint actual outputFuel header.function.resultType header.output (.value source) native added := by
  obtain ⟨payload, decoded, _imported⟩ := exported.reimports
  obtain ⟨_sourceType, imported⟩ := exported.reimports_payload requested decoded
  obtain ⟨actualSource, actualOutcome, represented, _heaps, _world, _returned, _related, _stable, _typed, valueTyped⟩ :=
    CellAwarePublicApplicationResult.named_returned_value result decoded
  have same : source = actualSource := Staging.Recursive.Outcome.value.inj actualOutcome
  subst actualSource
  obtain ⟨encoded, encodedAt, payloadAt⟩ := imported
  obtain ⟨added, selected, handles, _meanings⟩ := selection.collect represented valueTyped encodedAt rfl payloadAt
  have nativeValue : native = .inRight .word payload := by
    cases result.2.1 with
    | value represented =>
        simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
        exact congrArg (Core.Value.inRight .word) decoded
  exact ⟨payload, added, nativeValue, selected, handles, .select requested rfl nativeValue selection selected⟩

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- The actual export receipt collects all requested function leaves at the
Source-derived returned heap, without guessing a numeric sufficient budget. -/
theorem first_collected
    (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
      ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
        ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (payload : Core.Value) (added : List Entry),
          native = .inRight .word payload ∧
          RecursiveNamedPublicOutputSelections.Selected selection source payload header.output outputFuel added ∧
          added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached added := by
  obtain ⟨actual, generation, exported, atReturned⟩ :=
    CellAwarePublicNamedObservedOutput.actual_result atCheckpoint completed resumed
  refine ⟨actual,generation,exported,atReturned,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready),?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨payload,added,nativeValue,selectedLeaves,handles,addition⟩ :=
    selected_addition functions cells result requested exported selection
  obtain ⟨reached,related,post⟩ := result.2.2.2.2.2.2.2
  exact ⟨reached,payload,added,nativeValue,selectedLeaves,handles,related,
    ⟨.first rfl started selected exported result reached ⟨related,post⟩ addition,
      CellAwarePublicPhysicalHistory.physical_of_result physical result⟩⟩

include selected started exactRegistry ready atCheckpoint result completed resumed in
/-- Later observed output appends its selected function leaves while retaining
all previous entries and the exact current Source/native heap. -/
theorem after_collected {entries : List Entry}
    (history : CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
      (receiving := registry) (anchor := anchor) session mapping world before store caller entries) :
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration),
      checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore actual ∧
      completion.IndexedAt actual ∧ actual.session.RegistryAt registry ∧ actual.session.ExportsReady ∧
      ∀ selection : RecursiveNamedPublicOutputSelections.Selection header.function.resultType actual.value,
        ∃ (reached : Caller headers keys finalMap finalWorld after finalStore) (payload : Core.Value) (added : List Entry),
          native = .inRight .word payload ∧
          RecursiveNamedPublicOutputSelections.Selected selection source payload header.output outputFuel added ∧
          added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
          CellAwarePublicPhysicalHistory.History (functions := functions) (cells := cells)
            (receiving := registry) (anchor := anchor)
            actual.session finalMap finalWorld after finalStore reached (entries ++ added) := by
  obtain ⟨actual,generation,exported,atReturned⟩ :=
    CellAwarePublicNamedObservedOutput.actual_result atCheckpoint completed resumed
  refine ⟨actual,generation,exported,atReturned,
    exactRegistry.symm ▸ started.returned_registry exported,
    exported.exportsReady (started.original.initial_registry.exportsReady ready),?_⟩
  intro selection
  have atRecipe : artifact.RecipeAt recipe := by cases artifact; exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  rw [(RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2] at requested
  obtain ⟨payload,added,nativeValue,selectedLeaves,handles,addition⟩ :=
    selected_addition functions cells result requested exported selection
  obtain ⟨reached,related,post⟩ := result.2.2.2.2.2.2.2
  have retained := CellAwarePublicFunctionHistory.History.next history.semantic rfl started selected exported
    result reached ⟨related,post⟩ addition
  exact ⟨reached,payload,added,nativeValue,selectedLeaves,handles,related,history.after_result result retained⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNamedObservedCollection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
/-! A later real public start uses the heap and function history returned by
previous execution. Input encoding determines its new receiving registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} {rows : Inventory inputs}
  {prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe}
  {anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
  {cells : CellAwarePublicCells.Family (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).definitions}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}
  (state : CellAwarePublicSessionState.State rows functions cells anchor initial recipe session entries)
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)

structure Started where
  checkpoint : SourceCoreIndexedSession.Checkpoint state.artifact
  root : SourceCoreIndexedSession.Root recipe.compiled
  payloads : Environment
  encodedValues : SourceCoreCompatibleValues.Context
  atCheckpoint : call.checkpoint.IndexedAt checkpoint
  started : RecursiveNamedPublicStartMeaning.StartAt state.session key publicArguments
    options.inputValidationFuel checkpoint recipe root state.world state.store payloads encodedValues
  selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
    (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header

include prepared in
/-- The returned history fixes the actual world and store of this new start.
Selection only concerns the original root chosen by the requested key. -/
theorem from_call
    (selectRoot : ∀ root : SourceCoreIndexedSession.Root recipe.compiled,
      recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root →
      RecursiveNamedPublicRootMeaning.RootSelection
        (values := .initial recipe.compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
        (program := Program.ofChecked recipe.compiled.sourceProgram) (headers rows) root header) :
    Nonempty (Started (header := header) state call) := by
  obtain ⟨request, headerEq⟩ := RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with
    prepared inputs rows state.atRecipe state.history.semantic.current.1 state.atSession
    (fun _ actual => actual = header)
    (fun root selected => ⟨header, selectRoot root selected, rfl⟩) call.started
  exact ⟨⟨request.checkpoint, request.root, request.payloads, request.encodedValues,
    request.atCheckpoint, request.started, headerEq ▸ request.selected⟩⟩

structure Ready (start : Started (header := header) state call) (arguments : List Dynamic.Value) where
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  contextAt : receiving.result.context = start.encodedValues
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry
  history : CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys recipe.compiled)
    (functions := functions) (cells := cells receiving.result.context.registry)
    (receiving := receiving.result.context.registry) (anchor := anchor)
    state.session state.mapping state.world state.heap state.store state.caller entries
  stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows state.caller
  globalReference : (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)[header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
      ((owner recipe.compiled).key.locations header))
  heapTyped : Dynamic.HeapWellTyped header.function.context state.heap
  represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked receiving.result.context.registry functions)
    state.mapping state.world header.bindings arguments start.payloads
  argumentsTyped : Dynamic.ValuesHaveTypes header.function.context state.heap arguments header.types

/-- Metadata transport, current heap typing and data argument representation
follow from the real input encoder and the previously established history. -/
theorem of_started
    (covariant : CellAwarePublicCells.ExtendsRegistry cells)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (start : Started (header := header) state call)
    {arguments : List Dynamic.Value}
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments) :
    Nonempty (Ready state call start arguments) := by
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, _diagnostic⟩ :=
    CellAwarePublicActualRegistryStart.named_start covariant state.history.semantic state.registry start.started
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨represented, argumentsTyped⟩ :=
    SelectedCompilationPublicDataArgumentReceipts.data_arguments_at_receiving functions
      receiving.result.context.registry state.mapping state.heap start.started start.selected rfl
      (SelectedCompilationHeaderCertificates.certified bodyTyping header) metadata inputTypes inputMeanings
  have globals := CallableIndexedOwnedPhysicalCanonicalState.ordinary_slots
    (owner recipe.compiled) (by intro _ _; rfl)
    (CallableIndexedOwnedPhysicalGlobals.environment_slots recipe.compiled) header start.selected.member
  simp only [CallableIndexedOwnedPhysicalGlobals.environment, List.length_nil, Nat.zero_add] at globals
  exact ⟨⟨receiving, contextAt, issued, state.extension.trans extended,
    ⟨retained, state.history.physical⟩, retained.current.2.2.1, globals,
    retained.current.2.2.2.1.transportContext
      (SelectedCompilationPublicReturnedValues.header_context_supports anchor header bodyTyping).1,
    represented, argumentsTyped⟩⟩

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicNextStart
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedHandle
/-! The actual accepted direct-handle checkpoint and current public history
supply input, heap and captured Source typing for a retained materialized row.
The row is recovered from the positively retained output certificate. No
caller supplies an association or a call meaning. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedHandle
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
  (history : History headers keys functions
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
      (GeneralizedLocalInstanceValues.model recipe.compiled.indexed))
    completion.result.context.registry anchor session mapping world before store caller entries)
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

local notation "cells" => GeneralizedLocalDescriptorHeap.cellModel
  (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked completion.result.context.registry functions)
  (GeneralizedLocalInstanceValues.model recipe.compiled.indexed)
local notation "callStages" => SelectedCompilationPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bodyTyping history inHistory entryType sourceEq in
/-- Current retained typing identifies the actual Source frame before the
independent call trace is constructed. No completed target call is needed. -/
theorem source_frame : Dynamic.ClosureFrame (Program.ofChecked recipe.compiled.sourceProgram) function := by
  obtain ⟨_imported, _represented, typed⟩ := history.current.2.2.2.2 entry inHistory
  rw [entryType, sourceEq] at typed
  obtain ⟨_facts, certificate⟩ := SelectedCompilationHeaderCertificates.certified bodyTyping anchor
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  obtain ⟨_parameters, _result, signatures, sourceCode, evidence, _captures⟩ := typed.closure_function_inv
  exact ⟨signatures.trans runtime.signatures, sourceCode.owner, sourceCode,
    sourceCode.requirement_ledger.idsUnique, evidence⟩

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata in
/-- Finite completion of the original public checkpoint reconstructs the
materialized Source call using its current captures and packed input. -/
theorem completed_reflects {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore) (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
          anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwarePublicMaterializedHandleMeaning.completed_reflects functions profile receiver extension
    bodyTyping wellFormed history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata completed invocation

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata in
/-- A finite independent Source call supplies sufficient fuel for the same
accepted public checkpoint, including its exact failure store. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize invocation
      anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwarePublicMaterializedHandleMeaning.has_sufficient_fuel functions profile receiver extension
    bodyTyping wellFormed history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata packing arity trace

include profile receiver extension bodyTyping wellFormed history inHistory entryType sourceEq retained input started parameterView metadata in
/-- An ordinary independent Source call derives sufficient fuel for the
accepted public handle checkpoint. The exact result and reached heap embed
without a stage outcome because this retained body is a terminal read. -/
theorem source_has_sufficient_fuel {invocation : Staging.Recursive.Scope}
    {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource) (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked recipe.compiled.sourceProgram) sourceSize
      anchor.function.context callerEvidence invocationEvidence before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions cells caller anchor.function.context result nativeResult
        (Staging.Recursive.Lifting.embed outcome) after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨owner, bindings, parameterCore, resultCore, association, framed⟩ := retained.association sourceEq
  exact CellAwarePublicMaterializedHandleMeaning.source_has_sufficient_fuel (invocation := invocation) functions profile receiver extension
    bodyTyping wellFormed history entry inHistory entryType sourceEq association owner framed
    input started parameterView metadata packing arity trace

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicRetainedMaterializedHandle
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareReachedInvocationTerminals
/-! Actual accepted return and tail-expression compiler branches consume the
same smaller expression proof. The child certificate is exactly the policy
call retained by the accepted body tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareReachedInvocationTerminals
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationAcceptedTerminals (children)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {context : SourceSemantics.Context} {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index compiled ActualBodyInvocation.ReachedView}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep} {administrative : Core.Context}
  {scope : SourceCoreLocalCell.Scope} {id : StatementId} {statement : StatementNode} {stored : Core.Ty}
  {expression : ExpressionId} {node : ExpressionNode} {expected : TypeSystem.Ty}
  {lowered : SourceCoreBasic.LoweredExpr}

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

theorem returning {childFuel budget : Nat} {rest : List StatementId}
    (preserve : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reflect : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reached : index.Reached (.statement id))
    (source : invocation.source = index.source)
    (read : index.policy.readStatement index.compilerSource id = .ok (statement, stored))
    (form : statement.form = .returnStmt (some expression))
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope expression index.reasonAt = .ok lowered)
    (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) index.result lowered.type = .ok ())
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true (id :: rest) expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true (id :: rest) expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget := by
  rw [ensure_eq childType]
  have head := index.return_head_reached source reached rest read form
  exact ⟨CellAwareInvocationTerminalFlows.preserves bridge producer preserve source head generated found typed valueType,
    CellAwareInvocationTerminalFlows.reflects bridge producer reflect head generated found typed valueType⟩

theorem tail {childFuel budget : Nat}
    (preserve : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reflect : Dynamic.SourceRuntimeValid program context index.source →
      invocation.evidence.Covers context → context.solvedRequirements = index.compilation.solvedRequirements →
      CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation
        (children index childFuel) faults budget)
    (reached : index.Reached (.statement id))
    (source : invocation.source = index.source)
    (read : index.policy.readStatement index.compilerSource id = .ok (statement, stored))
    (form : statement.form = .expression expression false)
    (generated : index.policy.lowerExpression childFuel index.compilerSource scope expression index.reasonAt = .ok lowered)
    (childType : SourceCoreBasic.ensureType (.occurrence id.occurrence) index.result lowered.type = .ok ())
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (valueType : node.type = expected) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true [id] expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget ∧
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope true [id] expected index.result
      (LocalLoop.returnValue index.result lowered.expression) budget := by
  rw [ensure_eq childType]
  have head := index.tail_head_reached source reached read form
  exact ⟨CellAwareInvocationTerminalFlows.preserves bridge producer preserve source head generated found typed valueType,
    CellAwareInvocationTerminalFlows.reflects bridge producer reflect head generated found typed valueType⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareReachedInvocationTerminals
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
/-! The selected session fixes its actual positive function model and authentic
compiler-instance descriptor cells. Registry transport is derived internally. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {inputs : List (Input compiled)}

def functions (rows : Inventory inputs)
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CellAwarePhysicalFunctionOrigins.functions (headers rows) (keys compiled)
    initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) profile

def cells (rows : Inventory inputs)
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :=
  CellAwarePublicCells.generalized (functions rows initial profile)
    (GeneralizedLocalInstanceValues.model compiled.indexed)

abbrev State (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {publicArtifact : SourceCoreExecution.Artifact}
    (publicSession : SourceCoreExecution.Session publicArtifact) (entries : List Entry) :=
  CellAwarePublicSessionState.State rows (functions rows initial profile)
    (cells rows initial profile) anchor initial recipe publicSession entries

variable {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

/-- Actual named startup moves all retained entries to its real receiver. No
cell-transport law or call-body law is requested from the caller. -/
theorem State.at_named_request
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : State rows anchor initial profile recipe session entries)
    {checkpoint : SourceCoreExecution.Checkpoint artifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      checkpoint state.session key arguments inputFuel state.world state.store) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = request.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry ∧
      CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys compiled)
        (functions := functions rows initial profile)
        (cells := cells rows initial profile receiving.result.context.registry)
        (receiving := receiving.result.context.registry) (anchor := anchor)
        state.session state.mapping state.world state.heap state.store state.caller entries :=
  CellAwarePublicSessionState.State.at_named_request
    (CellAwarePublicCells.generalized_extends_registry _ _) prepared state request

/-- Actual packed input encoding reuses all current handle meanings, including
nested or repeated references, and retains the exact physical heap authority. -/
theorem State.at_packed_input
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : State rows anchor initial profile recipe session entries)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : SourceCoreIndexedSession.Checkpoint state.artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt state.session entry.handle
      argument inputFuel checkpoint recipe state.world state.store parameter result
      nativeParameter nativeResult callable packed encodedValues) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry ∧
      CellAwarePublicPhysicalHistory.History (headers := headers rows) (keys := keys compiled)
        (functions := functions rows initial profile)
        (cells := cells rows initial profile receiving.result.context.registry)
        (receiving := receiving.result.context.registry) (anchor := anchor)
        state.session state.mapping state.world state.heap state.store state.caller entries ∧
      CompatiblePayload.ValueRep compiled.compatible.checked receiving.result.context.registry
        (functions rows initial profile) state.mapping state.world
        sourceParameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context state.heap source sourceParameter ∧
      ∀ token, checkpoint.diagnostic token = .ok (receiving.result.diagnostics.diagnostic? token) := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, represented, typed, diagnostics⟩ :=
    CellAwarePublicActualRegistryStart.packed_input
      (CellAwarePublicCells.generalized_extends_registry _ _)
      state.history.semantic state.registry member entryType input started
  exact ⟨receiving, contextAt, issued, state.extension.trans extended,
    ⟨retained, state.history.physical⟩, represented, typed, diagnostics⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedPublicSessionState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CellAwareSelectedRootBounds
/-! The numeric family quantifies over roots with actual complete cache state.
Every invocation produces this same carrier through its parameter allocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSelectedRootBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open SelectedCompilationMixedRootSupport (RootAt)
open CellAwareStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (cells : GenericHeap.CellModel definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)
  (faults : RecursiveStageMeaning.FaultRep)

def PreservesRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    PreservesAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model cells stages invocation (Point scope expression lowered) faults size

def ReflectsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    ReflectsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model cells stages invocation (Point scope expression lowered) faults size

theorem preservesRootsAt_ordinary_iff (size : Nat) :
    PreservesRootsAt (headers := headers) (keys := keys) model (GenericHeap.CellModel.ordinary model)
      stages semanticFaults faults size ↔
    SelectedCompilationMixedRootBounds.PreservesRootsAt (headers := headers) (keys := keys) model
      stages semanticFaults faults size := by
  simp only [PreservesRootsAt, SelectedCompilationMixedRootBounds.PreservesRootsAt, CellAwareStagedExpressionBounds.preservesAt_ordinary_iff]

theorem reflectsRootsAt_ordinary_iff (size : Nat) :
    ReflectsRootsAt (headers := headers) (keys := keys) model (GenericHeap.CellModel.ordinary model)
      stages semanticFaults faults size ↔
    SelectedCompilationMixedRootBounds.ReflectsRootsAt (headers := headers) (keys := keys) model
      stages semanticFaults faults size := by
  simp only [ReflectsRootsAt, SelectedCompilationMixedRootBounds.ReflectsRootsAt, CellAwareStagedExpressionBounds.reflectsAt_ordinary_iff]

end Solcore.SourceSemantics.CoreLowering.CellAwareSelectedRootBounds
end
