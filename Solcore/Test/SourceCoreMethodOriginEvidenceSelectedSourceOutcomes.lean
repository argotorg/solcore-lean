import Solcore.Test.SourceCoreMethodOriginEvidenceSelectedCompilerProfile
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSourceOutcomes

/-! The actual seven-call compiler-profile session has independent Dynamic
outcomes at the same retained functions, dictionaries and reached heaps.
Its original sufficient-fuel conclusions remain attached to the same sequence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedSourceOutcomes
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SelectedCertified
open SelectedCompilationCertifiedPublicSession (Issued)
open RecursiveNamedPublicPhysicalSessionState (PlainValue)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {issued : Issued fixture.recipe}
  {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
  {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
  {useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow}
  {useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow}
  {sequence : ObservedSequence fixture observed}

structure DynamicMeaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) : Prop where
  first : PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] meaning.first.entry.source meaning.first.after.heap
  second : PlainValue meaning.first.initial.header meaning.second.request.header
    (RecursiveStageRegistry.scope boolStages.sidecar [] meaning.second.request.header.function)
    meaning.first.after.heap [.bool false, .bool true, .bool true] meaning.second.entry.source meaning.second.after.heap
  firstRead : PlainValue meaning.first.initial.header meaning.firstRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.firstRead.request.header.function)
    meaning.second.after.heap [meaning.first.entry.source] (.word (Core.Word.ofNatModulo 33)) meaning.firstRead.after.heap
  third : PlainValue meaning.first.initial.header meaning.third.request.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] meaning.third.request.header.function)
    meaning.firstRead.after.heap [.word (Core.Word.ofNatModulo 55), .word (Core.Word.ofNatModulo 66), .bool false]
    meaning.third.entry.source meaning.third.after.heap
  secondRead : PlainValue meaning.first.initial.header meaning.secondRead.request.header
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] meaning.secondRead.request.header.function)
    meaning.third.after.heap [meaning.second.entry.source] (.bool true) meaning.secondRead.after.heap
  repeatedRead : PlainValue meaning.first.initial.header meaning.repeatedRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.repeatedRead.request.header.function)
    meaning.secondRead.after.heap [meaning.first.entry.source] (.word (Core.Word.ofNatModulo 33)) meaning.repeatedRead.after.heap
  thirdRead : PlainValue meaning.first.initial.header meaning.thirdRead.request.header
    (RecursiveStageRegistry.scope useWordStages.sidecar [] meaning.thirdRead.request.header.function)
    meaning.repeatedRead.after.heap [meaning.third.entry.source] (.word (Core.Word.ofNatModulo 55)) meaning.thirdRead.after.heap

theorem dynamic_meaning
    (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence) :
    DynamicMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.second.trace.value_plain, meaning.firstRead.trace.value_plain,
    meaning.third.trace.value_plain, meaning.secondRead.trace.value_plain,
    meaning.repeatedRead.trace.value_plain, meaning.thirdRead.trace.value_plain⟩

/-- Both original checker budgets feed the actual common compiler profile.
The independent applications and the forward bounds use the same session witness. -/
theorem closed_outcomes
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (profile : SelectedCompilerProfile.Observed fixture)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe)
      (meaning : SequenceMeaning issued wordStages boolStages useWordStages useBoolStages sequence),
      DynamicMeaning meaning ∧ SelectedCertified.ForwardMeaning meaning ∧
      meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.first.entry.handle ≠ meaning.third.entry.handle ∧
      meaning.second.entry.handle ≠ meaning.third.entry.handle := by
  obtain ⟨issued, meaning, forward⟩ := SelectedCompilerProfile.closed_sequence_forward_meaning
    wordStages boolStages useWordStages useBoolStages profile checked sequence
  exact ⟨issued, meaning, dynamic_meaning meaning, forward, meaning.handles_distinct⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← SelectedCompilerProfile.observe fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _original := closed_outcomes wordStages boolStages useWordStages useBoolStages profile fixture.checked sequence
  let ⟨checked1000⟩ ← observeOriginalCheckAt1000 fixture
  have _companion := closed_outcomes wordStages boolStages useWordStages useBoolStages profile checked1000.accepted sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 12 && profile.value.table.rows.length == 10 do
    throw (IO.userError "ordinary source outcomes changed original cache12/table10")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,31,49,122,140,213,286,340] do
    throw (IO.userError s!"ordinary source outcomes changed original stores: {reprStr stores}")
  IO.println "SELECTED_METHOD_SOURCE_OUTCOMES_PASS: actual profile X7 at checker1024 and1000; seven independent Dynamic applications; exact named dictionaries, retained closures and Source heaps; scalar33/true/33/55; original stores and forward bounds"

end Tests.SourceCoreMethodOriginEvidence.SelectedSourceOutcomes
