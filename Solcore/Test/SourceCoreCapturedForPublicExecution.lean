import Solcore.Test.SourceCoreCapturedForInvocation
import Solcore.Test.SourceCoreCapturedForMakeStep
import Solcore.Test.SourceCoreCapturedForSeed
import Solcore.Test.SourceCoreCapturedForClosureShape

/-! The first captured cell is written and read again after a separate closure
and a fresh factory allocation. Every transition uses the actual returned
public session and the same Source heap retained by the previous call. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (firstEntry secondEntry thirdEntry : Entry) (firstClosure secondClosure : Dynamic.Closure),
      firstEntry.sourceType = .function (.product .bool (.product .word .bool)) .word ∧ firstEntry.handle = sequence.first.handle ∧
      secondEntry.sourceType = .function (.product .bool (.product .word .bool)) .word ∧ secondEntry.handle = sequence.second.handle ∧
      thirdEntry.sourceType = .function (.product .bool (.product .word .bool)) .word ∧ thirdEntry.handle = sequence.third.handle ∧
      firstEntry.handle ≠ secondEntry.handle ∧
      firstEntry.source = .closure firstClosure ∧ secondEntry.source = .closure secondClosure ∧
      firstClosure.parameters = [observed.running, observed.argument, observed.shape.stop] ∧ secondClosure.parameters = [observed.running, observed.argument, observed.shape.stop] ∧
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
        SourceInvocation support scope second.heap firstEntry.source true (Core.Word.ofNatModulo 11) false
          (.value (.word (Core.Word.ofNatModulo 10))) written.heap ∧
        SourceCall support support.actual.header scope written.heap [.word (Core.Word.ofNatModulo 30)]
          (.value thirdEntry.source) third.heap ∧
        SourceInvocation support scope third.heap secondEntry.source false (Core.Word.ofNatModulo 21) false
          (.value (.word (Core.Word.ofNatModulo 20))) other.heap ∧
        SourceInvocation support scope other.heap firstEntry.source true (Core.Word.ofNatModulo 12) false
          (.value (.word (Core.Word.ofNatModulo 11))) final.heap

/-- Accepted checker/compiler observations construct all static support. The
loop writes and reads the first capture again after independent activity. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning stages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := receiver.completion) fixture observed stages receiver.completion.result.context.registry
    (receiver.issued)
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
  have distinct : firstEntry.handle ≠ secondEntry.handle := by
    rw [firstHandle, secondHandle]
    exact sequence.distinct
  exact ⟨support, firstEntry, secondEntry, thirdEntry, firstClosure, secondClosure,
    firstType, firstHandle, secondType, secondHandle, thirdType, thirdHandle, distinct,
    firstSource, secondSource, firstParameters, secondParameters,
    first, second, written, third, other, final,
    firstTrace, secondTrace, writtenTrace, thirdTrace, otherTrace, finalTrace⟩

/-- All static and receiving evidence comes from the actual accepted compiler
and authentic registry. No external receiver or body meaning is required. -/
theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ receiver, SequenceMeaning stages sequence receiver := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed stages sequence receiver⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual captured for loops: make10/make20, first(true,11,false) returns10, make30, second(false,21,false) returns20, first(true,12,false) returns11; six Source calls and returned histories proved"

end Tests.SourceCoreCapturedFor
