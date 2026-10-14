import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicReturnedValues
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicClosureHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicScalarResults
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicDirectCallableHistory
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryStart
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs
import Solcore.SourceSemantics.Staging.SelectedRecursivePreservation

/-! Actual packed callable execution retains the complete physical cache and
all previous exports. The input encoder supplies the reached registry, and the
shared static package closes every body meaning used by reflection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectFailureStep
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

/-- Actual packed failure preserves the original callable, complete history and
heap effects. Its exact diagnostic distinguishes semantic and stage faults. -/
theorem State.invoke_failure
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
    {options : SourceCoreExecution.RunOptions}
    {returned : SourceCoreExecution.Session artifact} {reason : Word}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked compiled.sourceProgram) entry.source sources.length ∧
      ∃ failure, ∃ next : State rows anchor initial profile recipe returned entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages compiled) size
        invocation anchor.function.context state.heap entry.source sources (.fault failure) next.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        next.receiving.result.diagnostics failure reason := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
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
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    SelectedCompilationPublicDirectCallableHistory.completed_reflects_at_arity
      (completion := receiving) support issued (state.extension.trans extended)
      retained state.history.physical entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := resultAt.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  have diagnostic : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
      receiving.result.diagnostics failure reason := by
    have represented := resultAt.1
    cases represented with
    | fault matched =>
      have decoded := failed.2.1
      simp only [Core.LanguageResult.decode?] at decoded
      cases decoded
      exact matched
  have calleeTyped := (retained.current.2.2.2.2 entry member).2.2
  rw [entryType] at calleeTyped
  obtain ⟨_packedRelated, packedTyped⟩ :=
    started.history_input_compatible retained input parameterView metadata
  have preserved := Staging.Recursive.SelectedPreservation.applies_fault selectedBodies
    (SelectedCompilationPublicHistorySourceInputs.header_runtime support.bodyTyping anchor)
    retained.current.2.2.2.1 calleeTyped packing packedTyped trace
  obtain ⟨reached, _related, history⟩ :=
    retained.after_packed_failure started.original failed resultAt preserved.1
  have returnedRegistry : actual.RegistryAt encodedValues.registry := by
    exact congrArg SourceCoreCompatibleValues.Context.registry (failed.2.2.2.2.1.trans started.values)
  let next : State rows anchor initial profile recipe returned entries := {
    artifact := state.artifact
    session := actual
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := sessionAt
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ returnedRegistry
    history := ⟨history, state.history.physical.extend resultAt.2.2.2.2.1⟩ }
  exact ⟨sources, packing, arity, failure, next, sourceSize, trace, diagnostic⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectFailureStep
