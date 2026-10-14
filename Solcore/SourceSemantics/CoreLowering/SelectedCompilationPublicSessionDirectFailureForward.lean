import Solcore.Frontend.SourceCoreFailurePreservationReceipts
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalProgramSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectCallableHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs
import Solcore.SourceSemantics.Staging.SelectedRecursivePreservation

/-! Independent Source execution of a retained callable determines every
sufficiently funded direct public resume. The actual input encoder determines
the receiving registry; existing exports and the complete physical cache remain
in the returned session at the exact Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectFailureForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

def FailureForwardAt (rows : Inventory inputs)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (recipe : SourceCoreIndexedSession.Recipe)
    {artifact : SourceCoreExecution.Artifact}
    (entries : List Entry) (failure : Staging.Recursive.Failure)
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution token,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ returned : SourceCoreExecution.Session artifact,
        outcome = .failed token returned ∧ returned.ExportsReady ∧
        ∃ next : State rows anchor initial profile recipe returned entries,
          next.heap = after ∧
          CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
            next.receiving.result.diagnostics failure token

/-- A real packed start and independent Source fault determine actual public
failure at every sufficient execution budget and every output budget. -/
theorem forward_call
    (support : SelectedCompilationPhysicalProgramSupport.Support
      compiled (headers rows) (keys compiled) initial)
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled))
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    (state : State rows anchor initial profile recipe session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {inputFuel : Nat} {publicCheckpoint : SourceCoreExecution.Checkpoint artifact}
    (accepted : session.startHandlePacked entry.handle argument inputFuel = .ok publicCheckpoint)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages compiled) sourceSize
      invocation anchor.function.context state.heap entry.source sources (.fault failure) after) :
    FailureForwardAt rows anchor initial profile recipe entries failure publicCheckpoint after := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.semantic.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.semantic.current.1 imported original
  obtain ⟨receiving, _indexed, contextAt, issued, extended, retained, _represented, _typed, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input state.history.semantic state.registry
      member entryType input started
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨value, finalStore, finalMap, finalWorld, requiredExecution, enough, resultAt⟩ :=
    SelectedCompilationPublicDirectCallableHistory.has_sufficient_fuel_at_arity
      (completion := receiving) support issued (state.extension.trans extended)
      retained state.history.physical entry member entryType input
      started parameterView.symm metadata packing arity trace
  obtain ⟨token, rfl, faultRelated⟩ : ∃ token,
      value = .inLeft nativeResult (.word token) ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics failure token := by
    have represented := resultAt.1
    cases represented with
    | fault related => exact ⟨_, rfl, related⟩
  have calleeTyped := (retained.current.2.2.2.2 entry member).2.2
  rw [entryType] at calleeTyped
  obtain ⟨_packedRelated, packedTyped⟩ :=
    started.history_input_compatible retained input parameterView metadata
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor)
    retained.current.2.2.2.1 calleeTyped packing packedTyped trace
  have checkpointReady := started.original.initial_registry.exportsReady
    (state.atSession.exportsReady_iff.mp ready)
  refine ⟨requiredExecution, token, ?_⟩
  intro executionFuel outputFuel outcome executionBound resumed
  have completed := enough executionFuel executionBound
  obtain ⟨returned, outcomeEq⟩ := resumed.native_failed atCheckpoint completed rfl
  have failedResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed token returned) := outcomeEq ▸ resumed
  obtain ⟨actual, _generation, actualValue, actualStore, actualCompleted, failed, returnedAt⟩ :=
    failedResume.indexed_failed atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, _related, history⟩ :=
    retained.after_packed_failure started.original failed resultAt preserved.1
  have returnedRegistry : actual.RegistryAt encodedValues.registry :=
    congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans started.values)
  let next : State rows anchor initial profile recipe returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := ⟨history, state.history.physical.extend resultAt.2.2.2.2.1⟩ }
  exact ⟨returned, outcomeEq, returnedAt.exportsReady_iff.mpr (failed.exportsReady checkpointReady),
    next, rfl, faultRelated⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectFailureForward
