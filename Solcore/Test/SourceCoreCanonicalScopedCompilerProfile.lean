import Solcore.Test.SourceCoreCanonicalScopedCertifiedMeaning

/-! One actual complete compiler profile connects the unchanged six public
calls to Source execution, retained captures and all sufficient fuel bounds. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open SelectedCompilationCertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued stages sequence.first
  second : FunctionMeaning issued first.after stages secondSeed sequence.second
  firstRead : InvocationMeaning issued second.after first.entry firstNext true false
    sequence.firstRead seed (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  intervening : FunctionMeaning issued firstRead.after stages interveningSeed sequence.intervening
  secondRead : InvocationMeaning issued intervening.after second.entry secondNext true false
    sequence.secondRead secondSeed (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  repeatedRead : InvocationMeaning issued secondRead.after first.entry repeatedNext false false
    sequence.repeatedRead firstNext (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)

variable {issued : Issued fixture.recipe} {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

theorem SequenceMeaning.handles_distinct (meaning : SequenceMeaning issued stages sequence) :
    meaning.first.entry.handle ≠ meaning.second.entry.handle := by
  rw [meaning.first.handleEq, meaning.second.handleEq]
  exact sequence.distinct

theorem sequence_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe, Nonempty (SequenceMeaning issued stages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile stages sequence.first
  let scope := RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function
  obtain ⟨second⟩ := function_meaning first.after stages secondSeed sequence.second
  obtain ⟨firstRead⟩ := invocation_meaning second.after first.entry (by simp)
    first.entryType first.handleEq first.handleType firstNext true false sequence.firstRead seed sequence.firstValue scope
  obtain ⟨intervening⟩ := function_meaning firstRead.after stages interveningSeed sequence.intervening
  obtain ⟨secondRead⟩ := invocation_meaning intervening.after second.entry (by simp)
    second.entryType second.handleEq second.handleType secondNext true false sequence.secondRead secondSeed sequence.secondValue scope
  obtain ⟨repeatedRead⟩ := invocation_meaning secondRead.after first.entry (by simp)
    first.entryType first.handleEq first.handleType repeatedNext false false sequence.repeatedRead firstNext sequence.repeatedValue scope
  exact ⟨issued, ⟨⟨first, second, firstRead, intervening, secondRead, repeatedRead⟩⟩⟩

structure ForwardMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support (firstCall sequence.first).toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  second : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (functionCall sequence.second).toCall.toStartedCall parameterType .word meaning.second.entry.source meaning.second.after.heap
  firstRead : ∃ checkpoint, sequence.second.completion.session.startHandlePacked sequence.first.handle
      (packed firstNext true false) runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe ([meaning.first.entry] ++ [meaning.second.entry])
      (.word seed) checkpoint meaning.firstRead.after.heap
  intervening : SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt
    (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    (functionCall sequence.intervening).toCall.toStartedCall parameterType .word meaning.intervening.entry.source meaning.intervening.after.heap
  secondRead : ∃ checkpoint, sequence.intervening.completion.session.startHandlePacked sequence.second.handle
      (packed secondNext true false) runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.intervening.entry])
      (.word secondSeed) checkpoint meaning.secondRead.after.heap
  repeatedRead : ∃ checkpoint, sequence.secondRead.completion.session.startHandlePacked sequence.first.handle
      (packed repeatedNext false false) runOptions.inputValidationFuel = .ok checkpoint ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.intervening.entry])
      (.word firstNext) checkpoint meaning.repeatedRead.after.heap

theorem SequenceMeaning.forward (meaning : SequenceMeaning issued stages sequence) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 100000 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady interveningReady
  exact ⟨meaning.first.forward, meaning.second.forward firstReady, meaning.firstRead.forward secondReady,
    meaning.intervening.forward firstReadReady, meaning.secondRead.forward interveningReady,
    meaning.repeatedRead.forward secondReadReady⟩

theorem closed_sequence_forward_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      meaning.first.entry.handle ≠ meaning.second.entry.handle ∧ ForwardMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning profile stages sequence
  exact ⟨issued, meaning, meaning.handles_distinct, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 3 && profile.value.table.rows.length == 3 do
    throw (IO.userError "scoped closure profile changed original cache3/table3")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.intervening.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize]
  unless stores == [4,7,10,44,47,81,106] do
    throw (IO.userError s!"scoped closure profile stores changed: {reprStr stores}")
  IO.println "SCOPED_CLOSURE_PROFILE_FORWARD_PASS: original C6 at checker1000; one complete profile and automatic catalog; make10/make20/A10/make30/B20/A11; retained captures and related Source heaps; all six sufficient public fuel bounds; original stores"

end Tests.SourceCoreCanonicalScoped.CompilerProfile
