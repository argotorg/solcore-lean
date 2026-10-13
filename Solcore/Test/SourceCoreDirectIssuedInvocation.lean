import Solcore.Test.SourceCoreDirectIssuedIssuance
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectScalarStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning

/-! The same public proof consumes actual named and builtin handles. Argument
and callee representations are derived from their current retained history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SourceInvocation {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (source argument : Dynamic.Value)
    (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
    support.makeHeader.header.function.context before source [argument] (.value (.word word)) after

/-- Exact observed public completion fixes the Source result; structural input
receipts and the actual packed encoder fix the Source argument. -/
theorem invoke {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
    {entries : List Entry} (state : RetainedState support publicSession entries)
    (entry : Entry) (member : entry ∈ entries) {parameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter .word)
    {handle : SourceCorePublicValues.Handle} (entryHandle : entry.handle = handle)
    (handleType : handle.sourceType = .function parameter .word)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries
      support.makeHeader.header.function.context parameter argument source)
    (_simple : SourceCoreIndexedSession.FunctionTreeSimple argument)
    (singleton : ∀ sources, Dynamic.ValuesPack sources source → sources = [source])
    (call : ObservedInvocation publicSession handle argument)
    {word : Core.Word} (returned : call.completion.value = .word word)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceInvocation support invocation state.heap entry.source source word after.heap := by
  obtain ⟨sources, packing, _arity, next, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar support.program
      fixture.recipePrepared state entry member (.word word) entryType
      (entryHandle ▸ handleType) input (by simpa only [entryHandle] using call.executed)
      returned invocation
  exact ⟨next, size, singleton sources packing ▸ trace⟩


end Tests.SourceCoreDirectIssued
