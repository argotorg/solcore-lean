import Solcore.Test.SourceCoreCapturedAssignmentInvocation
import Solcore.Test.SourceCoreCapturedAssignmentMakeStep
import Solcore.Test.SourceCoreCapturedAssignmentSeed
import Solcore.Test.SourceCoreCapturedAssignmentClosureShape

/-! The first captured cell is written and read again after a separate closure
and a fresh factory allocation. Every transition uses the actual returned
public session and the same Source heap retained by the previous call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedAssignment
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (firstEntry secondEntry thirdEntry : Entry) (firstClosure secondClosure : Dynamic.Closure),
      firstEntry.sourceType = .function .word .word ∧ firstEntry.handle = sequence.first.handle ∧
      secondEntry.sourceType = .function .word .word ∧ secondEntry.handle = sequence.second.handle ∧
      thirdEntry.sourceType = .function .word .word ∧ thirdEntry.handle = sequence.third.handle ∧
      firstEntry.source = .closure firstClosure ∧ secondEntry.source = .closure secondClosure ∧
      firstClosure.parameters = [observed.argument] ∧ secondClosure.parameters = [observed.argument] ∧
      ∃ first : RetainedState support sequence.first.completion.session [firstEntry],
      ∃ second : RetainedState support sequence.second.completion.session [firstEntry, secondEntry],
      ∃ written : RetainedState support sequence.firstCall.completion.session [firstEntry, secondEntry],
      ∃ third : RetainedState support sequence.third.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ other : RetainedState support sequence.secondCall.completion.session [firstEntry, secondEntry, thirdEntry],
      ∃ final : RetainedState support sequence.firstAgain.completion.session [firstEntry, secondEntry, thirdEntry],
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed]
          (.value firstEntry.source) first.heap ∧
        SourceCall support support.actual.header scope first.heap [.word (Core.Word.ofNatModulo 20)]
          (.value secondEntry.source) second.heap ∧
        SourceInvocation support scope second.heap firstEntry.source (Core.Word.ofNatModulo 11)
          (.value (.word (Core.Word.ofNatModulo 10))) written.heap ∧
        SourceCall support support.actual.header scope written.heap [.word (Core.Word.ofNatModulo 30)]
          (.value thirdEntry.source) third.heap ∧
        SourceInvocation support scope third.heap secondEntry.source (Core.Word.ofNatModulo 21)
          (.value (.word (Core.Word.ofNatModulo 20))) other.heap ∧
        SourceInvocation support scope other.heap firstEntry.source (Core.Word.ofNatModulo 12)
          (.value (.word (Core.Word.ofNatModulo 11))) final.heap

/-- Accepted checker/compiler observations construct all static support. The
last returned eleven is the value written through the first handle earlier. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning stages sequence receiver := by
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨firstEntry, firstType, firstHandle, firstHandleType, first, firstTrace⟩ :=
    first_meaning support stages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨secondEntry, secondType, secondHandle, secondHandleType, second, secondTrace⟩ :=
    first.make_typed_handle sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨written, writtenTrace⟩ := invoke second firstEntry (by simp) firstType firstSource
    firstParameters firstHandle firstHandleType sequence.firstCall sequence.firstValue scope
  obtain ⟨thirdEntry, thirdType, thirdHandle, _thirdHandleType, third, thirdTrace⟩ :=
    written.make_typed_handle sequence.third scope
  obtain ⟨other, otherTrace⟩ := invoke third secondEntry (by simp) secondType secondSource
    secondParameters secondHandle secondHandleType sequence.secondCall sequence.secondValue scope
  obtain ⟨final, finalTrace⟩ := invoke other firstEntry (by simp) firstType firstSource
    firstParameters firstHandle firstHandleType sequence.firstAgain sequence.finalValue scope
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle,
    firstSource, secondSource, firstParameters, secondParameters,
    first, second, written, third, other, final,
    firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed stages sequence receiver
  IO.println "Actual captured assignment: make10/make20, first11 returns10, make30, second21 returns20, first12 returns11; six Source calls and returned histories proved"

end Tests.SourceCoreCapturedAssignment
