import Solcore.Test.SourceCoreRecursiveIndexCertifiedMeaning
import Solcore.Test.SourceCoreRecursiveIndexFailureStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionFailures

/-! Mapping inputs refer to the actual retained handles. Successful selections
append their real exports; a failed selection retains every prior entry and its
reached Source heap, together with the original public diagnostic relation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Profiled)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Profiled fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

theorem select_meaning (before : issued.toIssued.State anchor session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    (key : Core.Word)
    (call : ObservedFunctionCall session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (scope : Staging.Recursive.Scope) :
    Nonempty (FunctionMeaning issued before observed.selectRow call [sourceTable first second, .word key] scope) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.selectRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before call.toCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.selectRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [← actualEq, actual.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have raw : request.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.select_result_type
  obtain ⟨entry, type, handle, handleType, after, trace⟩ := issued.toIssued.reflect_function before call request inputs scope
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, handleType.trans raw, after, trace⟩⟩

def failureCall {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFailure session key arguments) :
    SelectedCompilationPublicSessionState.StartedCall session key arguments runOptions :=
  ⟨call.checkpoint, call.started⟩

structure FailureMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFailure session observed.selectRow.row.key publicArguments)
    (arguments : List Dynamic.Value) (scope : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session observed.selectRow.row.key publicArguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture observed.selectRow.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  failure : Staging.Recursive.Failure
  after : issued.toIssued.State anchor call.returned entries
  trace : SelectedCompilationPublicSessionState.SourceCall anchor request.header scope
    before.heap arguments (.fault failure) after.heap
  diagnostic : CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
    after.receiving.result.diagnostics failure call.reason

theorem failure_meaning (before : issued.toIssued.State anchor session entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    (key : Core.Word)
    (call : ObservedFailure session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (scope : Staging.Recursive.Scope) :
    Nonempty (FailureMeaning issued before call [sourceTable first second, .word key] scope) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.selectRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before (failureCall call) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.selectRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [← actualEq, actual.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  obtain ⟨failure, after, trace, diagnostic⟩ := issued.reflect_failure before (failureCall call)
    call.returned call.reason call.executed request inputs scope
  exact ⟨⟨request, actual, actualEq.symm, inputs, failure, after, trace, diagnostic⟩⟩

theorem FailureMeaning.forward {before : issued.toIssued.State anchor session entries}
    {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFailure session observed.selectRow.row.key publicArguments}
    {arguments : List Dynamic.Value} {scope : Staging.Recursive.Scope}
    (meaning : FailureMeaning issued before call arguments scope) (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionFailureForward.FailureForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      meaning.failure (failureCall call) meaning.after.heap :=
  issued.forward_failure before (failureCall call) meaning.request meaning.inputs ready meaning.trace

end Tests.SourceCoreRecursiveIndex.CompilerProfile
