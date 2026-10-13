import Solcore.Test.SourceCoreRecursiveIndexInitialForward
import Solcore.Test.SourceCoreRecursiveIndexInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionExportForward

/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry} {key : SourceCoreIndexedSession.Key}
    {arguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session key arguments)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after ∧
          ReturnedValue completion returned source outputFuel

theorem forward_make {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries) {value : Core.Word}
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation state.heap
      [.word value] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selectedHeader := selected_make_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word value] [.word value] := by
    rw [selectedHeader, support.makeHeader.make_input_types_source]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  have rawType : request.header.function.resultType = closureType := by
    rw [selectedHeader]
    exact support.makeHeader.make_result_type
  have applied : RecursiveNamedPublicPhysicalSessionState.SourceCall support.makeHeader.header request.header
      invocation state.heap [.word value] (.value source) after := by
    simpa only [selectedHeader] using trace
  have forwarded := RecursiveNamedPublicPhysicalSessionExportForward.forward_function_at_input_registry
    support.program fixture.recipePrepared state call.toCall.toStartedCall request inputs rawType ready applied
  simpa only [RecursiveNamedPublicPhysicalSessionExportForward.ForwardAt,
    RecursiveNamedPublicPhysicalSessionExportForward.ReturnedValue,
    PublicSupports.functions, RecursiveNamedPublicPhysicalSessionState.functions, RetainedState, ForwardAt, ReturnedValue,
    closureType] using forwarded


theorem forward_select {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    (first second : RecursiveNamedPublicFunctionHistory.Entry)
    (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFunctionCall session observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.selectHeader.header invocation state.heap
      [sourceTable first second, .word key] (.value source) after) :
    ForwardAt (entries := entries) support call source after := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selectedHeader := selected_select_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body))
      [table firstHandle secondHandle, .word key] [sourceTable first second, .word key] := by
    rw [selectedHeader, support.selectHeader.select_input_types_source]
    exact select_inputs first second firstMember secondMember firstType secondType firstHandleEq secondHandleEq key
  have rawType : request.header.function.resultType = closureType := by
    rw [selectedHeader]
    exact support.selectHeader.select_result_type
  have applied : RecursiveNamedPublicPhysicalSessionState.SourceCall support.makeHeader.header request.header
      invocation state.heap [sourceTable first second, .word key] (.value source) after := by
    simpa only [selectedHeader] using trace
  have forwarded := RecursiveNamedPublicPhysicalSessionExportForward.forward_function_at_input_registry
    support.program fixture.recipePrepared state call.toCall.toStartedCall request inputs rawType ready applied
  simpa only [RecursiveNamedPublicPhysicalSessionExportForward.ForwardAt,
    RecursiveNamedPublicPhysicalSessionExportForward.ReturnedValue,
    PublicSupports.functions, RecursiveNamedPublicPhysicalSessionState.functions, RetainedState, ForwardAt, ReturnedValue,
    closureType] using forwarded


end Tests.SourceCoreRecursiveIndex
