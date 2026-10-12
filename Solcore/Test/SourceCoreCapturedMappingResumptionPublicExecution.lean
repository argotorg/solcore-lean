import Solcore.Test.SourceCoreCapturedMappingResumptionRuntime

/-! Finite public resumptions retain the same independent Source execution,
current captured heap, authentic receiver, and reusable function history.
The forward guarantee concerns total execution fuel and the final output budget. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedMappingResumption
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedMapping
open RecursiveNamedPublicFunctionHistory (Entry)

def ForwardChainWordAt {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} (checkpoint : SourceCoreExecution.Checkpoint artifact)
    (entries : List Entry) (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      checkpoint.ResumeChain executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = .word word ∧ completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

/-- Collapse changes neither the actual terminal outcome nor the export event.
Intermediate output budgets are irrelevant because those events exhausted execution fuel. -/
theorem forward_chain {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {checkpoint : SourceCoreExecution.Checkpoint artifact} {entries : List Entry}
    {handle : SourceCorePublicValues.Handle} {argument : List (Core.Word × Core.Word)}
    {word : Core.Word} {after : Dynamic.Heap}
    (started : session.startHandlePacked handle (publicArgument argument)
      runOptions.inputValidationFuel = .ok checkpoint)
    (forward : ForwardWordAt support session entries handle argument word after) :
    ForwardChainWordAt support checkpoint entries word after := by
  obtain ⟨original, accepted, requiredExecution, requiredOutput, enough⟩ := forward
  have same : original = checkpoint := Except.ok.inj (accepted.symm.trans started)
  subst original
  exact ⟨requiredExecution, requiredOutput, fun executionFuel outputFuel outcome
    enoughExecution enoughOutput chain =>
      enough executionFuel outputFuel outcome enoughExecution enoughOutput chain.collapse⟩

/-- All Source traces and retained states come from the actual checker/compiler,
bootstrap, and two resumed calls. No Source execution or export-success law is assumed. -/
theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ResumedSequence fixture observed) :
    sequence.first.checkpoint.ResumeChain runOptions.executionFuel runOptions.outputValidationFuel
      (.succeeded sequence.first.completion) ∧
    sequence.second.checkpoint.ResumeChain runOptions.executionFuel runOptions.outputValidationFuel
      (.succeeded sequence.second.completion) ∧
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver),
      let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
      ∃ entry : Entry,
        entry.sourceType = .function (.mapping .word .word) .word ∧ entry.handle = sequence.factory.handle ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source firstArgument (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source secondArgument (.value (.word seed)) final.heap ∧
        ForwardChainWordAt support sequence.first.checkpoint [entry] seed first.heap ∧
        ForwardChainWordAt support sequence.second.checkpoint [entry] seed final.heap := by
  obtain ⟨receiver, support, entry, entryType, handle, initial, first, final,
    factoryTrace, firstTrace, secondTrace, firstForward, secondForward⟩ :=
    closed_sequence_forward_meaning fixture observed stages sequence.observed
  exact ⟨sequence.first.chain, sequence.second.chain,
    receiver, support, entry, entryType, handle, initial, first, final,
    factoryTrace, firstTrace, secondTrace,
    forward_chain sequence.first.started firstForward,
    forward_chain sequence.second.started secondForward⟩

/-- One factory and two direct calls; each direct call has two genuine positive
fuel exhaustion events before its final completion. -/
def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeResumedSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual mapping closure resumptions: two positive exhaustion events per call, captured 10/10, Source and sufficient-total-fuel histories proved"

end Tests.SourceCoreCapturedMappingResumption
