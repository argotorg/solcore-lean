import Solcore.Test.SourceCoreCapturedCopyInvocation
import Solcore.Test.SourceCoreCapturedCopySeed
import Solcore.Test.SourceCoreCapturedCopyMakeStep
import Solcore.Test.SourceCoreCapturedCopyClosureShape

/-! Three actual factory executions and three direct public handle invocations
retain distinct captures through intervening calls, with independent Source
applications and exact returned histories for the complete sequence. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedCopy
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (makeStages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.actual.header.function
    ∃ first second intervening : Entry,
      first.sourceType = .function .unit .word ∧ second.sourceType = .function .unit .word ∧
      intervening.sourceType = .function .unit .word ∧
      first.handle = sequence.first.handle ∧ second.handle = sequence.second.handle ∧
      intervening.handle = sequence.intervening.handle ∧ first.handle ≠ second.handle ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ secondState : RetainedState support sequence.second.completion.session [first, second],
      ∃ firstInvokedState : RetainedState support sequence.invokeFirst.completion.session [first, second],
      ∃ interveningState : RetainedState support sequence.intervening.completion.session [first, second, intervening],
      ∃ secondInvokedState : RetainedState support sequence.invokeSecond.completion.session [first, second, intervening],
      ∃ finalState : RetainedState support sequence.invokeFirstAgain.completion.session [first, second, intervening],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceCall support support.actual.header scope firstState.heap [.word secondSeed]
          (.value second.source) secondState.heap ∧
        SourceInvocation support scope secondState.heap first.source
          (.value (.word seed)) firstInvokedState.heap ∧
        SourceCall support support.actual.header scope firstInvokedState.heap [.word interveningSeed]
          (.value intervening.source) interveningState.heap ∧
        SourceInvocation support scope interveningState.heap second.source
          (.value (.word secondSeed)) secondInvokedState.heap ∧
        SourceInvocation support scope secondInvokedState.heap first.source
          (.value (.word seed)) finalState.heap

/-- Every initial state, callable, capture, argument and result belongs to the
original actual public execution; semantic body laws are constructed internally. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (makeStages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages sequence receiver := by
  obtain ⟨support⟩ := static_supports fixture observed makeStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.actual.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, firstState, firstTrace⟩ :=
    first_meaning support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    firstState.make_typed_handle sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨firstInvokedState, firstInvokedTrace⟩ := invoke secondState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirst sequence.firstValue scope
  obtain ⟨intervening, interveningType, interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstInvokedState.make_typed_handle sequence.intervening scope
  obtain ⟨secondInvokedState, secondInvokedTrace⟩ := invoke interveningState second (by simp)
    secondType secondSource secondParameters secondHandle secondHandleType sequence.invokeSecond sequence.secondValue scope
  obtain ⟨finalState, finalTrace⟩ := invoke secondInvokedState first (by simp)
    firstType firstSource firstParameters firstHandle firstHandleType sequence.invokeFirstAgain sequence.firstValueAgain scope
  refine ⟨support, first, second, intervening, firstType, secondType, interveningType,
    firstHandle, secondHandle, interveningHandle, ?_, firstState, secondState, firstInvokedState,
    interveningState, secondInvokedState, finalState, firstTrace, secondTrace, firstInvokedTrace,
    interveningTrace, secondInvokedTrace, finalTrace⟩
  rw [firstHandle, secondHandle]
  exact sequence.distinct

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let makeStages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed makeStages sequence receiver
  IO.println "Actual closure body local: six public calls, independent captures 10/20, intervening make(30), Source results and returned histories proved"

end Tests.SourceCoreCapturedCopy
