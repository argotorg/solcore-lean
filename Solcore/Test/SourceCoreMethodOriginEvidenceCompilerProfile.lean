import Solcore.Test.SourceCoreMethodOriginEvidenceCertifiedSequence
import Solcore.Test.SourceCoreMethodOriginEvidenceFuelFixture
import Solcore.SourceSemantics.CoreLowering.CompilerCertifiedPublicSession

/-! One executable profile of the original complete cache supplies the automatic
public catalog. All seven Source calls use the same physical session, including
retained closures and both genuine original checker budgets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Certified
open CertifiedPublicSession (Issued)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original complete compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

theorem first_meaning
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨issued, initial, namedEq⟩ := CertifiedPublicSession.from_profile_initial_row
    (by rw [fixture.sameProgram]; exact checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value fixture.source_wellFormed first.opened
    first.as_function_call.toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 102400 first.session from .single first.ready)
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    initial.start.selected.member namedEq
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      initial.header.types := by
    rw [← actualEq, actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := first.as_function_call) (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  refine ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, ?_, handle, after, trace⟩⟩⟩
  exact type.trans (by rw [← actualEq]; exact actual.word_result_type)

theorem sequence_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe,
      Nonempty (SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile checked wordStages sequence.first
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

theorem closed_sequence_forward_meaning
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      Certified.ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning wordStages boolStages useWordStages useBoolStages profile checked sequence
  exact ⟨issued, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _original := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages
    profile fixture.checked sequence
  let ⟨checked1000⟩ ← observeOriginalCheckAt1000 fixture
  have _companion := closed_sequence_forward_meaning wordStages boolStages useWordStages useBoolStages
    profile checked1000.accepted sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 12 && profile.value.table.rows.length == 10 do
    throw (IO.userError "compiler profile changed original cache12/table10")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,31,49,122,140,213,286,340] do
    throw (IO.userError s!"compiler profile stores changed: {reprStr stores}")
  IO.println "COMPILER_PROFILE_FORWARD_PASS: one actual complete profile; original X7 at checker1024 and1000; all seven Source traces and sufficient public fuel bounds; one automatic catalog; retained closures; scalar33/true/33/55; original stores"

end Tests.SourceCoreMethodOriginEvidence.CompilerProfile
