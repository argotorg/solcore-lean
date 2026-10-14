import Solcore.Test.SourceCoreMethodOriginEvidenceSelectedCertifiedCalls

/-! The unchanged seven public calls share one automatic catalog and retain
all three closures through subsequent calls and sufficient-fuel resumptions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedCertified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMethodOriginEvidence.Certified (selected_row header_of_member)
open SelectedCompilationCertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued wordStages sequence.first
  second : FunctionMeaning issued first.after observed.boolRow.toObservedRow boolStages sequence.second .bool
    [.bool false, .bool true, .bool true]
  firstRead : ScalarMeaning issued second.after observed.useWordRow.toObservedRow useWordStages sequence.firstRead
    (.word (Core.Word.ofNatModulo 33)) [first.entry.source]
  third : FunctionMeaning issued firstRead.after observed.wordRow.toObservedRow wordStages sequence.third .word
    [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
  secondRead : ScalarMeaning issued third.after observed.useBoolRow.toObservedRow useBoolStages sequence.secondRead
    (.bool true) [second.entry.source]
  repeatedRead : ScalarMeaning issued secondRead.after observed.useWordRow.toObservedRow useWordStages sequence.repeatedRead
    (.word (Core.Word.ofNatModulo 33)) [first.entry.source]
  thirdRead : ScalarMeaning issued repeatedRead.after observed.useWordRow.toObservedRow useWordStages sequence.thirdRead
    (.word (Core.Word.ofNatModulo 55)) [third.entry.source]

variable {issued : Issued fixture.recipe}
  {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
  {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
  {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
  {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
  {sequence : ObservedSequence fixture observed}

theorem SequenceMeaning.handles_distinct
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.first.entry.handle ≠ meaning.third.entry.handle ∧
      meaning.second.entry.handle ≠ meaning.third.entry.handle := by
  rw [meaning.first.handleEq, meaning.second.handleEq, meaning.third.handleEq]
  exact ⟨sequence.firstSecond, sequence.firstThird, sequence.secondThird⟩

theorem sequence_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe,
      Nonempty (SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning admission wordStages sequence.first
  obtain ⟨second⟩ := bool_meaning first.after false true true sequence.second boolStages
  obtain ⟨firstRead⟩ := useWord_meaning second.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.firstRead sequence.firstValue useWordStages
  obtain ⟨third⟩ := word_meaning firstRead.after (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false
    sequence.third wordStages
  obtain ⟨secondRead⟩ := useBool_meaning third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
  obtain ⟨repeatedRead⟩ := useWord_meaning secondRead.after first.entry
    (by simp) first.entryType first.handleEq (Core.Word.ofNatModulo 33)
    sequence.repeatedRead sequence.repeatedValue useWordStages
  obtain ⟨thirdRead⟩ := useWord_meaning repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55)
    sequence.thirdRead sequence.thirdValue useWordStages
  exact ⟨issued, ⟨⟨first, second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩⟩

structure ForwardMeaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) : Prop where
  first : SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support sequence.first.as_function_call.toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  second : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.second.toCall.toStartedCall .unit .bool meaning.second.entry.source meaning.second.after.heap
  firstRead : SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 33)) sequence.firstRead.toStartedCall meaning.firstRead.after.heap
  third : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.third.toCall.toStartedCall .unit .word meaning.third.entry.source meaning.third.after.heap
  secondRead : SelectedCompilationPublicSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.bool true) sequence.secondRead.toStartedCall meaning.secondRead.after.heap
  repeatedRead : SelectedCompilationPublicSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 33)) sequence.repeatedRead.toStartedCall meaning.repeatedRead.after.heap
  thirdRead : SelectedCompilationPublicSessionScalarForward.ForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.third.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (.word (Core.Word.ofNatModulo 55)) sequence.thirdRead.toStartedCall meaning.thirdRead.after.heap

theorem SequenceMeaning.forward
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨meaning.first.forward, meaning.second.forward firstReady, meaning.firstRead.forward secondReady,
    meaning.third.forward firstReadReady, meaning.secondRead.forward thirdReady,
    meaning.repeatedRead.forward secondReadReady, meaning.thirdRead.forward repeatedReady⟩

theorem closed_sequence_forward_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning wordStages boolStages useWordStages useBoolStages admission sequence
  exact ⟨issued, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _certified := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages admission sequence
  have _original := Tests.SourceCoreMethodOriginEvidence.closed_sequence_forward_meaning fixture observed
    wordStages boolStages useWordStages useBoolStages admission sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,31,49,122,140,213,286,340] do
    throw (IO.userError s!"certified catalog stores changed: {reprStr stores}")
  IO.println "CERTIFIED_CATALOG_FORWARD_PASS: original seven Source calls and sufficient public fuel bounds; one automatic catalog; three distinct retained closures; scalar33/true/33/55; related Source heaps and original public stores"

end Tests.SourceCoreMethodOriginEvidence.SelectedCertified
