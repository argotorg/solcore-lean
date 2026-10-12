import Solcore.Test.SourceCoreDirectOutputFactory
import Solcore.Test.SourceCoreCapturedReuseSeed
import Solcore.Test.SourceCoreCapturedReuseClosureShape
import Solcore.Test.SourceCoreCapturedDirectInvocation

/-! A direct named factory export becomes a later direct-call input, preserving
both the new capture and the earlier capture through intervening executions. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectOutput
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    ∃ first named second : Entry,
      first.sourceType = .function .unit .word ∧
      named.sourceType = .function .word (.function .unit .word) ∧
      second.sourceType = .function .unit .word ∧
      first.handle = sequence.first.handle ∧ named.handle = sequence.named.handle ∧
      second.handle = sequence.second.handle ∧ first.handle ≠ second.handle ∧
      named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.makePacket.header.named.specialized support.makeInput.prepared.available)) ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ namedState : RetainedState support sequence.named.completion.session [first, named],
      ∃ secondState : RetainedState support sequence.second.completion.session [first, named, second],
      ∃ firstInvokedState : RetainedState support sequence.invokeFirst.completion.session [first, named, second],
      ∃ secondInvokedState : RetainedState support sequence.invokeSecond.completion.session [first, named, second],
      ∃ finalState : RetainedState support sequence.invokeFirstAgain.completion.session [first, named, second],
        namedState.heap = firstState.heap ∧
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceCall support support.makeHeader.header scope namedState.heap [.word secondSeed]
          (.value second.source) secondState.heap ∧
        Tests.SourceCoreCapturedDirect.SourceInvocation support scope secondState.heap first.source
          (.value (.word seed)) firstInvokedState.heap ∧
        Tests.SourceCoreCapturedDirect.SourceInvocation support scope firstInvokedState.heap second.source
          (.value (.word secondSeed)) secondInvokedState.heap ∧
        Tests.SourceCoreCapturedDirect.SourceInvocation support scope secondInvokedState.heap first.source
          (.value (.word seed)) finalState.heap

/-- The real public output encoder supplies the newly remembered entry, which
is reused with the original capture in the actual returned sessions. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages sequence receiver := by
  obtain ⟨support⟩ := static_supports fixture observed extra makeStages readStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, firstState, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨named, namedType, namedHandle, namedHandleType, namedSource, namedState, namedHeap⟩ :=
    remember_named firstState sequence.named
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    invoke_factory namedState named (by simp) namedType namedSource namedHandle namedHandleType sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨firstInvokedState, firstInvokedTrace⟩ := Tests.SourceCoreCapturedDirect.invoke secondState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirst sequence.firstValue scope
  obtain ⟨secondInvokedState, secondInvokedTrace⟩ := Tests.SourceCoreCapturedDirect.invoke firstInvokedState second (by simp)
    secondType secondSource secondParameters secondHandle secondHandleType sequence.invokeSecond sequence.secondValue scope
  obtain ⟨finalState, finalTrace⟩ := Tests.SourceCoreCapturedDirect.invoke secondInvokedState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirstAgain sequence.firstValueAgain scope
  refine ⟨support, first, named, second, firstType, namedType, secondType,
    firstHandle, namedHandle, secondHandle, ?_, namedSource,
    firstState, namedState, secondState, firstInvokedState, secondInvokedState, finalState,
    namedHeap, firstTrace, secondTrace, firstInvokedTrace, secondInvokedTrace, finalTrace⟩
  rw [firstHandle, secondHandle]
  exact sequence.distinct

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual direct factory output: collected make(20), reused captures 10/20/10, Source arguments/results and returned histories proved"

end Tests.SourceCoreDirectOutput
