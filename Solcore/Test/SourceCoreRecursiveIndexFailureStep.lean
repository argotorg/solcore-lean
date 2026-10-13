import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionRegistryFailureStep
import Solcore.Test.SourceCoreRecursiveIndexInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedReflection

/-! The failed index call keeps the exact current encoder registry and all
older handle captures. The Source failure remains related to the actual token;
no injectivity assumption about diagnostic tokens is required. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {artifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session artifact} {entries : List Entry}

/-- The actual failed public call retains export authority for the next call. -/
theorem ObservedFailure.exportsReady {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFailure session key arguments) (ready : session.ExportsReady) :
    call.returned.ExportsReady := by
  have compiledAt : ∃ compiled, artifact.CompiledAt compiled := by
    rcases artifact with ⟨compiled, opened⟩
    exact ⟨compiled, rfl⟩
  obtain ⟨compiled, compiledAt⟩ := compiledAt
  obtain ⟨checkpoint, started, resumed⟩ := call.executed
  obtain ⟨_recipe, _native, indexedSession, indexedCheckpoint, _opened, atSession, atCheckpoint, actualStart⟩ :=
    SourceCoreExecution.Session.start_indexed (compiled := compiled) compiledAt started
  obtain ⟨actual, _generation, _value, _store, _completed, failed, returnedAt⟩ :=
    resumed.indexed_failed atCheckpoint
  exact returnedAt.exportsReady_iff.mpr (failed.exportsReady
    ((indexedSession.start_root_receipt actualStart).initial_registry.exportsReady
      (atSession.exportsReady_iff.mp ready)))

theorem RetainedState.select_failure
    (state : RetainedState support session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.returned entries, ∃ failure,
      SourceCall support support.selectHeader.header invocation state.heap
        [sourceTable first second, .word key] (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics
        failure call.reason := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput]
    support.rows support.complete state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader
    support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selected, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have descriptor : SourceCoreCallableContracts.Descriptor
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact support.selectDescriptor
  let started : RecursiveNamedPublicPhysicalSessionState.StartedCall session observed.selectRow.row.key
      [table firstHandle secondHandle, .word key] runOptions := ⟨call.checkpoint, call.started⟩
  obtain ⟨failure, after, trace, decoded⟩ :=
    RecursiveNamedPublicPhysicalSessionFailureStep.State.failed_call_at_input_registry
      support.program fixture.recipePrepared state started call.returned call.reason call.executed
      request inputs descriptor invocation
  exact ⟨after, failure, by simpa only [selected] using trace, decoded⟩

end Tests.SourceCoreRecursiveIndex
