import Solcore.Test.SourceCoreRecursiveIndexSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionInitialExportForward

/-! Independent nested-direct Source success gives execution and export bounds
at the real first checkpoint, with the exact returned heap and a usable handle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The returned public value reimports to the exact represented Source result. -/
def ReturnedValue {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} (completion : SourceCoreExecution.Completion artifact)
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support completion.session entries) (source : Dynamic.Value) (fuel : Nat) : Prop :=
  ∃ payload nativeType,
    state.session.EncodesAt fuel closureType completion.value payload ∧
    CompatiblePayload.ValueRep fixture.recipe.compiled.compatible.checked state.receiving.result.context.registry
      support.functions state.mapping state.world closureType source payload nativeType

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow) (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        ∃ handle, completion.value = .function handle ∧ handle.sourceType = closureType ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after ∧ ReturnedValue completion returned source outputFuel

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.makeRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall support support.makeHeader.header invocation ⟨[]⟩ [.word seed] (.value source) after) :
    InitialForwardAt support first source after := by
  obtain ⟨start⟩ := first.initial_start support
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      support.makeHeader.header.function.context [.word seed] support.makeHeader.header.types := by
    rw [support.makeHeader.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have functionResult : SourceCoreRawMetadata.runtimeType support.makeHeader.header.function.resultType = .function .unit .word := by
    rw [support.makeHeader.make_result_type]
    rfl
  have forwarded := RecursiveNamedPublicPhysicalSessionInitialExportForward.first_function
    support.rows fixture.recipePrepared support.makeHeader.header support.makeHeader.header support.program
    support.distinct first.as_function_call.toCall.toStartedCall start
    (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes inputMeanings functionResult trace
  simpa only [RecursiveNamedPublicPhysicalSessionExportForward.ForwardAt,
    RecursiveNamedPublicPhysicalSessionExportForward.ReturnedValue,
    PublicSupports.functions, RecursiveNamedPublicPhysicalSessionState.functions, RetainedState, InitialForwardAt, ReturnedValue,
    ObservedPublicRun.as_function_call, support.makeHeader.make_result_type] using forwarded

end Tests.SourceCoreRecursiveIndex
