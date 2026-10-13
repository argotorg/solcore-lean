import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionRegistryFunctionStep
import Solcore.Test.SourceCoreRecursiveIndexInputs
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedStart
import Solcore.Test.SourceCoreRecursiveIndexSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry

/-! A genuine successful public selection extends the current retained
history with its actual selected closure. The next state is the returned session,
including the original captured heap and encoder metadata. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact}
  {publicSession : SourceCoreExecution.Session publicArtifact} {entries : List Entry}

/-- An actual public mapping selection constructs Source execution and the next history.
Every older entry remains in order, followed by this call's exported handle. -/
theorem RetainedState.select_typed_handle
    (state : RetainedState support publicSession entries)
    (first second : Entry) (firstMember : first ∈ entries) (secondMember : second ∈ entries)
    (firstType : first.sourceType = closureType) (secondType : second.sourceType = closureType)
    {firstHandle secondHandle : SourceCorePublicValues.Handle}
    (firstHandleEq : first.handle = firstHandle) (secondHandleEq : second.handle = secondHandle)
    {key : Core.Word}
    (call : ObservedFunctionCall publicSession observed.selectRow.row.key [table firstHandle secondHandle, .word key])
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : Entry, entry.sourceType = .function .unit .word ∧ entry.handle = call.handle ∧
      call.handle.sourceType = .function .unit .word ∧
      ∃ after : RetainedState support call.completion.session (entries ++ [entry]),
        SourceCall support support.selectHeader.header invocation state.heap [sourceTable first second, .word key]
          (.value entry.source) after.heap := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.makeInput, support.echoInput, support.chooseInput, support.selectInput] support.rows support.complete
    state.atRecipe state.history.semantic.current.1 state.atSession call.started
  have selected := selected_select_at support.makeHeader support.echoHeader support.chooseHeader support.selectHeader support.header_list request
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
  obtain ⟨entry, type, handle, handleType, after, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionFunctionStep.State.make_typed_handle_at_input_registry
      support.program fixture.recipePrepared state call request inputs descriptor invocation
  have resultType : request.header.function.resultType = .function .unit .word := by
    rw [selected]
    exact support.selectHeader.select_result_type
  exact ⟨entry, type.trans resultType, handle, handleType.trans resultType, after,
    by simpa only [selected] using trace⟩

end Tests.SourceCoreRecursiveIndex
