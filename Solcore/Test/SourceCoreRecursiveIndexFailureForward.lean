import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionRegistryFailureForward
import Solcore.Test.SourceCoreRecursiveIndexFailureStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-! Independent Source failure fixes a sufficient execution budget at the
original public checkpoint. Every output budget, including zero, retains the
same reached Source heap, current diagnostic registry and earlier handles. -/
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

def ForwardFailureAt (support : PublicSupports receiver)
    {firstHandle secondHandle : SourceCorePublicValues.Handle} {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) (entries : List Entry) : Prop :=
  ∃ token required,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      required ≤ executionFuel → call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ returned : SourceCoreExecution.Session artifact,
        outcome = .failed token returned ∧ returned.ExportsReady ∧
        ∃ state : RetainedState support returned entries, state.heap = after ∧
          CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics failure token

theorem forward_failure
    (state : RetainedState support session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [sourceTable first second, .word key] (.fault failure) after) :
    ForwardFailureAt support call failure after entries := by
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
  let started : RecursiveNamedPublicPhysicalSessionState.StartedCall session observed.selectRow.row.key
      [table firstHandle secondHandle, .word key] runOptions := ⟨call.checkpoint, call.started⟩
  obtain ⟨required, token, enough⟩ :=
    RecursiveNamedPublicPhysicalSessionFailureForward.forward_call_at_input_registry
      support.program fixture.recipePrepared state started request inputs ready (by simpa only [selected] using trace)
  exact ⟨token, required, enough⟩

end Tests.SourceCoreRecursiveIndex
