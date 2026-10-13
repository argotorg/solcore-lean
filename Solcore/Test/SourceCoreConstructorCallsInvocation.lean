import Solcore.Test.SourceCoreConstructorCallsCommon
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectScalarStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectSuccessStep

/-! Collected closure handles use the current metadata receiver.
Each returned state retains that receiver for the following public call. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source : Dynamic.Value)
    (arguments : List Dynamic.Value) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source arguments outcome after

/-- Current history supplies the callee; literal input rows supply its argument.
No registry equality, arbitrary receiving table or metadata extension is assumed. -/
theorem invoke_word {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value (.word word)) after.heap := by
  obtain ⟨sources, packing, _arity, next, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar support.program
      fixture.recipePrepared state entry member (.word word) entryType
      (entryHandle ▸ handleType) input (by simpa only [entryHandle] using call.executed)
      returned invocation
  exact ⟨sources, next, packing, size, trace⟩


/-- Successful intervening execution retains the complete old history even
when its new result is left unselected. The actual Source value is still kept. -/
theorem invoke_success {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument packedSource)
    (call : ObservedInvocation publicSession handle argument)
    (invocation : Staging.Recursive.Scope) :
    ∃ (sources : List Dynamic.Value) (source : Dynamic.Value)
      (after : RetainedState support call.completion.session entries),
      Dynamic.ValuesPack sources packedSource ∧
      SourceInvocation support invocation state.heap entry.source sources (.value source) after.heap := by
  obtain ⟨sources, packing, _arity, source, next, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectSuccessStep.State.invoke_success support.program
      fixture.recipePrepared state entry member entryType input
      (by simpa only [entryHandle] using call.executed) invocation
  exact ⟨sources, source, next, packing, size, trace⟩

end Tests.SourceCoreConstructorCalls
