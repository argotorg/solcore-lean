import Solcore.Test.SourceCoreRecursiveIndexPublicExecution
import Solcore.Test.SourceCoreRecursiveIndexSuccessForward
import Solcore.Test.SourceCoreRecursiveIndexInvocationForward
import Solcore.Test.SourceCoreRecursiveIndexFailureForward

/-! Every successful step in the checked mapping sequence has independent
Source-to-public bounds at its original start, including the call after failure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering

def SuccessfulForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  InitialForwardAt meaning.support sequence.first meaning.first.source meaning.initial.heap ∧
  ForwardAt (entries := [meaning.first]) meaning.support sequence.second meaning.second.source meaning.secondState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second]) meaning.support sequence.firstSelect
    meaning.firstSelected.source meaning.firstSelectState.heap ∧
  ForwardWordAt meaning.support sequence.firstSelect.completion.session
    [meaning.first, meaning.second, meaning.firstSelected] sequence.firstSelect.handle seed meaning.firstReadState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second, meaning.firstSelected]) meaning.support sequence.intervening
    meaning.intervening.source meaning.interveningState.heap ∧
  ForwardAt (entries := [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening])
    meaning.support sequence.secondSelect meaning.secondSelected.source meaning.secondSelectState.heap ∧
  ForwardWordAt meaning.support sequence.secondSelect.completion.session
    [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening, meaning.secondSelected]
    sequence.secondSelect.handle secondSeed meaning.secondReadState.heap ∧
  ForwardWordAt meaning.support sequence.failed.returned
    [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening, meaning.secondSelected]
    sequence.first.handle seed meaning.finalState.heap

theorem SequenceWitness.successes_forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : SuccessfulForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstSelectReady := sequence.firstSelect.executed.exportsReady secondReady
  have firstReadReady := sequence.firstRead.executed.exportsReady firstSelectReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondSelectReady := sequence.secondSelect.executed.exportsReady interveningReady
  have secondReadReady := sequence.secondRead.executed.exportsReady secondSelectReady
  have failedReady := sequence.failed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    forward_make meaning.initial sequence.second firstReady meaning.secondTrace,
    forward_select meaning.secondState meaning.first meaning.second (by simp) (by simp)
      meaning.firstType meaning.secondType meaning.firstHandle meaning.secondHandle
      sequence.firstSelect secondReady meaning.firstSelectTrace,
    forward_word meaning.firstSelectState meaning.firstSelected (by simp)
      meaning.firstSelectedType meaning.firstSelectedHandle meaning.firstSelectedHandleType
      sequence.firstRead firstSelectReady meaning.firstPacking meaning.firstReadTrace,
    forward_make meaning.firstReadState sequence.intervening firstReadReady meaning.interveningTrace,
    forward_select meaning.interveningState meaning.first meaning.second (by simp) (by simp)
      meaning.firstType meaning.secondType meaning.firstHandle meaning.secondHandle
      sequence.secondSelect interveningReady meaning.secondSelectTrace,
    forward_word meaning.secondSelectState meaning.secondSelected (by simp)
      meaning.secondSelectedType meaning.secondSelectedHandle meaning.secondSelectedHandleType
      sequence.secondRead secondSelectReady meaning.secondPacking meaning.secondReadTrace,
    forward_word meaning.failedState meaning.first (by simp)
      meaning.firstType meaning.firstHandle meaning.firstHandleType
      sequence.repeatedRead failedReady meaning.repeatedPacking meaning.repeatedReadTrace⟩


def ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : Prop :=
  SuccessfulForwardMeaning meaning ∧
  ForwardFailureAt meaning.support sequence.failed meaning.failure meaning.failedState.heap
    [meaning.first, meaning.second, meaning.firstSelected, meaning.intervening, meaning.secondSelected]

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages sequence receiver) : ForwardMeaning meaning := by
  have ready := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady ready
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstSelectReady := sequence.firstSelect.executed.exportsReady secondReady
  have firstReadReady := sequence.firstRead.executed.exportsReady firstSelectReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondSelectReady := sequence.secondSelect.executed.exportsReady interveningReady
  have secondReadReady := sequence.secondRead.executed.exportsReady secondSelectReady
  exact ⟨meaning.successes_forward,
    forward_failure meaning.secondReadState meaning.first meaning.second (by simp) (by simp)
      meaning.firstType meaning.secondType meaning.firstHandle meaning.secondHandle
      sequence.failed secondReadReady meaning.failedTrace⟩

/-- The real accepted program and its observed executions close both directions:
all nine actual steps have Source traces, and each trace implies public progress
at sufficient fuel on the original checkpoint, including the missing-key fault. -/
theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      ∃ meaning : SequenceWitness makeStages sequence receiver, ForwardMeaning meaning := by
  obtain ⟨receiver, meaning⟩ :=
    closed_sequence_meaning fixture observed extra makeStages echoStages chooseStages selectStages sequence
  obtain ⟨meaning⟩ := meaning
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let echoStages ← observeStages fixture observed.echoRow
  let chooseStages ← observeStages fixture observed.chooseRow
  let selectStages ← observeStages fixture observed.selectRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed extra makeStages echoStages chooseStages selectStages sequence
  IO.println "Recursive echo(table)[choose(key)]: select A10, allocate30, select B20, missing key, reuse A10; all nine Source traces and public fuel bounds proved"

end Tests.SourceCoreRecursiveIndex
