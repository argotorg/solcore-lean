import Solcore.Test.SourceCoreRecursiveIndexCertifiedSelection
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSourceOutcomes

/-! The original mapping sequence uses one automatic compiler profile and
catalog. A missing key retains all five exports, their captures and the reached
Source heap, from which the original first handle is invoked again. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued stages sequence.first
  second : FunctionMeaning issued first.after observed.makeRow sequence.second [.word secondSeed]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  firstSelect : FunctionMeaning issued second.after observed.selectRow sequence.firstSelect
    [sourceTable first.entry second.entry, .word firstKey]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  firstRead : InvocationMeaning issued firstSelect.after firstSelect.entry sequence.firstRead seed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  intervening : FunctionMeaning issued firstRead.after observed.makeRow sequence.intervening [.word interveningSeed]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  secondSelect : FunctionMeaning issued intervening.after observed.selectRow sequence.secondSelect
    [sourceTable first.entry second.entry, .word secondKey]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  secondRead : InvocationMeaning issued secondSelect.after secondSelect.entry sequence.secondRead secondSeed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  failed : FailureMeaning issued secondRead.after sequence.failed
    [sourceTable first.entry second.entry, .word missingKey]
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  repeatedRead : InvocationMeaning issued failed.after first.entry sequence.repeatedRead seed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)

variable {issued : Issued fixture.recipe} {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

theorem SequenceMeaning.selected_handles (meaning : SequenceMeaning issued stages sequence) :
    meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
    meaning.firstSelect.entry.handle = meaning.first.entry.handle ∧
    meaning.secondSelect.entry.handle = meaning.second.entry.handle := by
  rw [meaning.first.handleEq, meaning.second.handleEq, meaning.firstSelect.handleEq, meaning.secondSelect.handleEq]
  exact ⟨sequence.distinct, sequence.firstSame, sequence.secondSame⟩

theorem SequenceMeaning.original_diagnostic (_meaning : SequenceMeaning issued stages sequence) :
    sequence.failed.checkpoint.diagnostic sequence.failed.reason = .ok (some {
      error := .typeMismatch closureType none
      site := .occurrence observed.selectShape.value.node.id.occurrence
      span := some observed.selectShape.value.node.span }) := by
  rw [sequence.failed.decoded, sequence.missingDiagnostic]

theorem sequence_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe, Nonempty (SequenceMeaning issued stages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile stages sequence.first
  let scope := RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function
  obtain ⟨second⟩ := make_meaning first.after secondSeed sequence.second scope
  obtain ⟨firstSelect⟩ := select_meaning second.after first.entry second.entry (by simp) (by simp)
    first.entryType second.entryType first.handleEq second.handleEq firstKey sequence.firstSelect scope
  obtain ⟨firstRead⟩ := invocation_meaning firstSelect.after firstSelect.entry (by simp)
    firstSelect.entryType firstSelect.handleEq firstSelect.handleType sequence.firstRead seed sequence.firstValue scope
  obtain ⟨intervening⟩ := make_meaning firstRead.after interveningSeed sequence.intervening scope
  obtain ⟨secondSelect⟩ := select_meaning intervening.after first.entry second.entry (by simp) (by simp)
    first.entryType second.entryType first.handleEq second.handleEq secondKey sequence.secondSelect scope
  obtain ⟨secondRead⟩ := invocation_meaning secondSelect.after secondSelect.entry (by simp)
    secondSelect.entryType secondSelect.handleEq secondSelect.handleType sequence.secondRead secondSeed sequence.secondValue scope
  obtain ⟨failed⟩ := failure_meaning secondRead.after first.entry second.entry (by simp) (by simp)
    first.entryType second.entryType first.handleEq second.handleEq missingKey sequence.failed scope
  obtain ⟨repeatedRead⟩ := invocation_meaning failed.after first.entry (by simp)
    first.entryType first.handleEq first.handleType sequence.repeatedRead seed sequence.repeatedValue scope
  exact ⟨issued, ⟨⟨first, second, firstSelect, firstRead, intervening, secondSelect, secondRead, failed, repeatedRead⟩⟩⟩

/-- Every completed ordinary application keeps the same arguments, callable
value, full dictionary and heap. A staging rejection keeps its actual guard. -/
structure PlainMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : RecursiveNamedPublicPhysicalSessionState.PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed] meaning.first.entry.source meaning.first.after.heap
  second : RecursiveNamedPublicPhysicalSessionState.PlainValue meaning.first.initial.header meaning.second.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.first.after.heap [.word secondSeed] meaning.second.entry.source meaning.second.after.heap
  firstSelect : RecursiveNamedPublicPhysicalSessionState.PlainValue meaning.first.initial.header meaning.firstSelect.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.second.after.heap [sourceTable meaning.first.entry meaning.second.entry, .word firstKey]
    meaning.firstSelect.entry.source meaning.firstSelect.after.heap
  firstRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.firstSelect.entry.source)
    meaning.firstSelect.after.heap meaning.firstSelect.entry.source meaning.firstRead.arguments
    (.word seed) meaning.firstRead.after.heap
  intervening : RecursiveNamedPublicPhysicalSessionState.PlainValue meaning.first.initial.header meaning.intervening.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.firstRead.after.heap [.word interveningSeed] meaning.intervening.entry.source meaning.intervening.after.heap
  secondSelect : RecursiveNamedPublicPhysicalSessionState.PlainValue meaning.first.initial.header meaning.secondSelect.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.intervening.after.heap [sourceTable meaning.first.entry meaning.second.entry, .word secondKey]
    meaning.secondSelect.entry.source meaning.secondSelect.after.heap
  secondRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.secondSelect.entry.source)
    meaning.secondSelect.after.heap meaning.secondSelect.entry.source meaning.secondRead.arguments
    (.word secondSeed) meaning.secondRead.after.heap
  failed : RecursiveNamedPublicPhysicalSessionState.FailureProjection
    meaning.first.initial.header meaning.failed.request.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    meaning.secondRead.after.heap [sourceTable meaning.first.entry meaning.second.entry, .word missingKey]
    meaning.failed.failure meaning.failed.after.heap
  repeatedRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.first.entry.source)
    meaning.failed.after.heap meaning.first.entry.source meaning.repeatedRead.arguments
    (.word seed) meaning.repeatedRead.after.heap

theorem SequenceMeaning.plain (meaning : SequenceMeaning issued stages sequence) : PlainMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.second.trace.value_plain, meaning.firstSelect.trace.value_plain,
    meaning.firstRead.trace.sound.value_plain, meaning.intervening.trace.value_plain,
    meaning.secondSelect.trace.value_plain, meaning.secondRead.trace.sound.value_plain,
    meaning.failed.trace.failure_plain, meaning.repeatedRead.trace.sound.value_plain⟩

structure ForwardMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : RecursiveNamedPublicPhysicalSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support (firstCall sequence.first).toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  second : RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := [meaning.first.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.second.toCall.toStartedCall .unit .word meaning.second.entry.source meaning.second.after.heap
  firstSelect : RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt
    (entries := [meaning.first.entry] ++ [meaning.second.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.firstSelect.toCall.toStartedCall .unit .word meaning.firstSelect.entry.source meaning.firstSelect.after.heap
  firstRead : ∃ checkpoint, sequence.firstSelect.completion.session.startHandlePacked sequence.firstSelect.handle
      .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    RecursiveNamedPublicPhysicalSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe
      (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry])
      (.word seed) checkpoint meaning.firstRead.after.heap
  intervening : RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt
    (entries := ([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.intervening.toCall.toStartedCall .unit .word meaning.intervening.entry.source meaning.intervening.after.heap
  secondSelect : RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt
    (entries := (([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    sequence.secondSelect.toCall.toStartedCall .unit .word meaning.secondSelect.entry.source meaning.secondSelect.after.heap
  secondRead : ∃ checkpoint, sequence.secondSelect.completion.session.startHandlePacked sequence.secondSelect.handle
      .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    RecursiveNamedPublicPhysicalSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe
      ((([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry] ++ [meaning.secondSelect.entry])
      (.word secondSeed) checkpoint meaning.secondRead.after.heap
  failed : RecursiveNamedPublicPhysicalSessionFailureForward.FailureForwardAt
    (entries := ((([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry]) ++ [meaning.secondSelect.entry])
    issued.catalog.rows meaning.first.initial.header issued.initial issued.support.profile fixture.recipe
    meaning.failed.failure (failureCall sequence.failed) meaning.failed.after.heap
  repeatedRead : ∃ checkpoint, sequence.failed.returned.startHandlePacked sequence.first.handle
      .unit runOptions.inputValidationFuel = .ok checkpoint ∧
    RecursiveNamedPublicPhysicalSessionDirectScalarForward.ForwardAt issued.catalog.rows meaning.first.initial.header
      issued.initial issued.support.profile fixture.recipe
      ((([meaning.first.entry] ++ [meaning.second.entry]) ++ [meaning.firstSelect.entry]) ++ [meaning.intervening.entry] ++ [meaning.secondSelect.entry])
      (.word seed) checkpoint meaning.repeatedRead.after.heap

theorem SequenceMeaning.forward (meaning : SequenceMeaning issued stages sequence) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 100000 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstSelectReady := sequence.firstSelect.executed.exportsReady secondReady
  have firstReadReady := sequence.firstRead.executed.exportsReady firstSelectReady
  have interveningReady := sequence.intervening.executed.exportsReady firstReadReady
  have secondSelectReady := sequence.secondSelect.executed.exportsReady interveningReady
  have secondReadReady := sequence.secondRead.executed.exportsReady secondSelectReady
  have failedReady := sequence.failed.exportsReady secondReadReady
  exact ⟨meaning.first.forward, meaning.second.forward firstReady, meaning.firstSelect.forward secondReady,
    meaning.firstRead.forward firstSelectReady, meaning.intervening.forward firstReadReady,
    meaning.secondSelect.forward interveningReady, meaning.secondRead.forward secondSelectReady,
    meaning.failed.forward secondReadReady, meaning.repeatedRead.forward failedReady⟩

theorem closed_sequence_forward_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      meaning.first.entry.handle ≠ meaning.second.entry.handle ∧
      meaning.firstSelect.entry.handle = meaning.first.entry.handle ∧
      meaning.secondSelect.entry.handle = meaning.second.entry.handle ∧
      ForwardMeaning meaning ∧ PlainMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning profile stages sequence
  obtain ⟨distinct, firstSame, secondSame⟩ := meaning.selected_handles
  exact ⟨issued, meaning, distinct, firstSame, secondSame, meaning.forward, meaning.plain⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 4 && profile.value.table.rows.length == 4 do
    throw (IO.userError "index profile changed original cache4/table4")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstSelect.completion.session.heapSize,
    sequence.firstRead.completion.session.heapSize, sequence.intervening.completion.session.heapSize,
    sequence.secondSelect.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.failed.returned.heapSize, sequence.repeatedRead.completion.session.heapSize]
  unless stores == [5,8,11,25,25,28,42,42,56,56] do
    throw (IO.userError s!"index profile stores changed: {reprStr stores}")
  IO.println s!"INDEX_COMPILER_PROFILE_FORWARD_PASS: original checker1000/cache4/table4; one complete profile and automatic catalog; original nine operations, independent Dynamic outcomes and all sufficient public fuel bounds; mapping selections A10/B20; missing-key diagnostic; old A10 after failure; stores {reprStr stores}"

end Tests.SourceCoreRecursiveIndex.CompilerProfile
