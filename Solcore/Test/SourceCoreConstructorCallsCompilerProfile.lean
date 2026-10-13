import Solcore.Test.SourceCoreConstructorCallsCertifiedCalls
import Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSourceOutcomes

/-! One checked compiler profile supplies the complete catalog and physical
support for the original nine constructor operations and their nested exports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
namespace Tests.SourceCoreConstructorCalls.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open CertifiedPublicSession (Issued)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure SequenceMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) where
  first : FirstMeaning issued stages sequence.first
  factory : NamedMeaning issued first.after observed.makeRow sequence.factory
  builtin : BuiltinMeaning issued factory.after sequence.builtin
  named : NamedMeaning issued builtin.after observed.readRow sequence.named
  construction : ConstructionMeaning issued named.after named.entry factory.entry first.entry builtin.entry sequence.construction
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  newRead : WordMeaning issued construction.after construction.collected.newEntry .unit .unit sequence.newRead secondSeed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  intervening : SuccessMeaning issued newRead.after construction.collected.factoryEntry .word closureType
    (.word interveningSeed) sequence.intervening
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  priorRead : WordMeaning issued intervening.after construction.collected.priorEntry .unit .unit sequence.priorRead seed
    (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)
  builtinRead : WordMeaning issued priorRead.after construction.collected.builtinEntry .integer (.integer 37) sequence.builtinRead
    (Core.Word.ofNatModulo 37) (RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function)

variable {issued : Issued fixture.recipe} {stages : ObservedStages fixture observed.makeRow}
  {sequence : ObservedSequence fixture observed}

theorem sequence_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ issued : Issued fixture.recipe, Nonempty (SequenceMeaning issued stages sequence) := by
  obtain ⟨issued, ⟨first⟩⟩ := first_meaning profile stages sequence.first
  let scope := RecursiveStageRegistry.scope stages.sidecar [] first.initial.header.function
  obtain ⟨factory⟩ := named_meaning first.after observed.makeRow sequence.factory
  obtain ⟨builtin⟩ := builtin_meaning factory.after sequence.builtin
  obtain ⟨named⟩ := named_meaning builtin.after observed.readRow sequence.named
  obtain ⟨construction⟩ := construction_meaning named.after named.entry factory.entry first.entry builtin.entry
    (by simp) (by simp) (by simp) (by simp)
    (named.entryType.trans named.selected.read_type) (factory.entryType.trans factory.selected.make_type)
    first.entryType builtin.entryType named.handleEq factory.handleEq first.handleEq builtin.handleEq sequence.construction scope
  have newMember : construction.collected.newEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have priorMember : construction.collected.priorEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have factoryMember : construction.collected.factoryEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have builtinMember : construction.collected.builtinEntry ∈
      ((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added := by
    simp [construction.collected.ordered]
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      (((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added)
      first.initial.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have wordInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      (((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added)
      first.initial.header.function.context .word (.word interveningSeed) (.word interveningSeed) :=
    .data ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
      ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      (((([first.entry] ++ [factory.entry]) ++ [builtin.entry]) ++ [named.entry]) ++ construction.added)
      first.initial.header.function.context .integer (.integer 37) (.integer 37) :=
    .data ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
      ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
  obtain ⟨newRead⟩ := word_meaning construction.after construction.collected.newEntry newMember
    construction.collected.newType construction.collected.newHandle sequence.construction.newType unitInput
    sequence.newRead sequence.newValue scope
  obtain ⟨intervening⟩ := success_meaning newRead.after construction.collected.factoryEntry factoryMember
    construction.collected.factoryType construction.collected.factoryHandle wordInput sequence.intervening scope
  obtain ⟨priorRead⟩ := word_meaning intervening.after construction.collected.priorEntry priorMember
    construction.collected.priorType construction.collected.priorHandle sequence.construction.priorType unitInput
    sequence.priorRead sequence.priorValue scope
  obtain ⟨builtinRead⟩ := word_meaning priorRead.after construction.collected.builtinEntry builtinMember
    construction.collected.builtinType construction.collected.builtinHandle sequence.construction.builtinType integerInput
    sequence.builtinRead sequence.builtinValue scope
  exact ⟨issued, ⟨⟨first, factory, builtin, named, construction, newRead, intervening, priorRead, builtinRead⟩⟩⟩

theorem SequenceMeaning.issuance_heap (meaning : SequenceMeaning issued stages sequence) :
    meaning.named.after.heap = meaning.first.after.heap :=
  meaning.named.heapEq.trans (meaning.builtin.heapEq.trans meaning.factory.heapEq)

theorem SequenceMeaning.selected_handles (meaning : SequenceMeaning issued stages sequence) :
    meaning.construction.collected.newEntry.handle ≠ meaning.construction.collected.priorEntry.handle ∧
    meaning.construction.collected.priorEntry.handle = meaning.first.entry.handle ∧
    meaning.construction.collected.factoryEntry.handle = meaning.factory.entry.handle ∧
    meaning.construction.collected.builtinEntry.handle = meaning.builtin.entry.handle := by
  rw [meaning.construction.collected.newHandle, meaning.construction.collected.priorHandle,
    meaning.construction.collected.factoryHandle, meaning.construction.collected.builtinHandle,
    meaning.first.handleEq, meaning.factory.handleEq, meaning.builtin.handleEq]
  exact ⟨sequence.construction.distinct, sequence.construction.priorSame,
    sequence.construction.factorySame, sequence.construction.builtinSame⟩

/-- Six executions have ordinary Dynamic meanings. The three intervening
issuances retain their exact Source callable identities and unchanged heaps. -/
structure PlainMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : RecursiveNamedPublicPhysicalSessionState.PlainValue meaning.first.initial.header meaning.first.initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function)
    ⟨[]⟩ [.word seed] meaning.first.entry.source meaning.first.after.heap
  construction : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.named.entry.source)
    meaning.named.after.heap meaning.named.entry.source meaning.construction.arguments
    meaning.construction.source meaning.construction.after.heap
  newRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.newEntry.source)
    meaning.construction.after.heap meaning.construction.collected.newEntry.source meaning.newRead.arguments
    (.word secondSeed) meaning.newRead.after.heap
  intervening : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.factoryEntry.source)
    meaning.newRead.after.heap meaning.construction.collected.factoryEntry.source meaning.intervening.arguments
    meaning.intervening.source meaning.intervening.after.heap
  priorRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.priorEntry.source)
    meaning.intervening.after.heap meaning.construction.collected.priorEntry.source meaning.priorRead.arguments
    (.word seed) meaning.priorRead.after.heap
  builtinRead : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    meaning.first.initial.header.function.context
    (RecursiveStageRegistry.scope stages.sidecar [] meaning.first.initial.header.function).evidence
    (Staging.Recursive.callableEvidence meaning.construction.collected.builtinEntry.source)
    meaning.priorRead.after.heap meaning.construction.collected.builtinEntry.source meaning.builtinRead.arguments
    (.word (Core.Word.ofNatModulo 37)) meaning.builtinRead.after.heap

theorem SequenceMeaning.plain (meaning : SequenceMeaning issued stages sequence) : PlainMeaning meaning :=
  ⟨meaning.first.trace.value_plain, meaning.construction.trace.sound.value_plain,
    meaning.newRead.trace.sound.value_plain, meaning.intervening.trace.sound.value_plain,
    meaning.priorRead.trace.sound.value_plain, meaning.builtinRead.trace.sound.value_plain⟩

section Forward
variable {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry} {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}

def OutputForward (_before : issued.State anchor session entries)
    (_call : ObservedInvocation session handle argument) (result : TypeSystem.Ty)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    RecursiveNamedPublicPhysicalSessionDirectOutputForward.ForwardAt issued.catalog.rows anchor
      issued.initial issued.support.profile fixture.recipe entries result checkpoint source after

def WordForward (_before : issued.State anchor session entries)
    (_call : ObservedInvocation session handle argument) (word : Core.Word) (after : Dynamic.Heap) : Prop :=
  ∃ checkpoint, session.startHandlePacked handle argument runOptions.inputValidationFuel = .ok checkpoint ∧
    RecursiveNamedPublicPhysicalSessionDirectWordForward.ForwardAt issued.catalog.rows anchor
      issued.initial issued.support.profile fixture.recipe entries word checkpoint after
end Forward

structure ForwardMeaning (meaning : SequenceMeaning issued stages sequence) : Prop where
  first : RecursiveNamedPublicPhysicalSessionInitialForward.ForwardAt issued.catalog.rows meaning.first.initial.header
    meaning.first.initial.header issued.support (firstCall sequence.first).toCall.toStartedCall
    meaning.first.entry.source meaning.first.after.heap
  construction : OutputForward meaning.named.after sequence.construction.toObservedInvocation
    (containerType fixture.dataType) meaning.construction.source meaning.construction.after.heap
  newRead : WordForward meaning.construction.after sequence.newRead secondSeed meaning.newRead.after.heap
  intervening : OutputForward meaning.newRead.after sequence.intervening closureType meaning.intervening.source meaning.intervening.after.heap
  priorRead : WordForward meaning.intervening.after sequence.priorRead seed meaning.priorRead.after.heap
  builtinRead : WordForward meaning.priorRead.after sequence.builtinRead (Core.Word.ofNatModulo 37) meaning.builtinRead.after.heap

theorem SequenceMeaning.forward (meaning : SequenceMeaning issued stages sequence) : ForwardMeaning meaning := by
  have initialReady := (SourceCoreExecution.Bootstrap.ReadyAt.single sequence.first.ready).exportsReady sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have factoryReady := sequence.factory.issued.exportsReady firstReady
  have builtinReady := sequence.builtin.issued.exportsReady factoryReady
  have namedReady := sequence.named.issued.exportsReady builtinReady
  have constructionReady := sequence.construction.executed.exportsReady namedReady
  have newReady := sequence.newRead.executed.exportsReady constructionReady
  exact ⟨meaning.first.forward, meaning.construction.forward namedReady, meaning.newRead.forward,
    meaning.intervening.forward newReady, meaning.priorRead.forward, meaning.builtinRead.forward⟩

theorem closed_sequence_forward_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow) (sequence : ObservedSequence fixture observed) :
    ∃ (issued : Issued fixture.recipe) (meaning : SequenceMeaning issued stages sequence),
      meaning.named.after.heap = meaning.first.after.heap ∧
      meaning.construction.collected.newEntry.handle ≠ meaning.construction.collected.priorEntry.handle ∧
      meaning.construction.collected.priorEntry.handle = meaning.first.entry.handle ∧
      meaning.construction.collected.factoryEntry.handle = meaning.factory.entry.handle ∧
      meaning.construction.collected.builtinEntry.handle = meaning.builtin.entry.handle ∧
      ForwardMeaning meaning ∧ PlainMeaning meaning := by
  obtain ⟨issued, ⟨meaning⟩⟩ := sequence_meaning profile stages sequence
  obtain ⟨distinct, prior, factory, builtin⟩ := meaning.selected_handles
  exact ⟨issued, meaning, meaning.issuance_heap, distinct, prior, factory, builtin, meaning.forward, meaning.plain⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let profile ← observe fixture
  let stages ← observeStages fixture observed.makeRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning profile stages sequence
  unless fixture.recipe.compiled.indexed.base.functions.length == 2 && profile.value.table.rows.length == 2 do
    throw (IO.userError "constructor profile changed original cache2/table2")
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.factory.completion.session.heapSize, sequence.builtin.completion.session.heapSize,
    sequence.named.completion.session.heapSize, sequence.construction.completion.session.heapSize,
    sequence.newRead.completion.session.heapSize, sequence.intervening.completion.session.heapSize,
    sequence.priorRead.completion.session.heapSize, sequence.builtinRead.completion.session.heapSize]
  unless stores == [3,6,6,6,6,21,21,24,24,24] do
    throw (IO.userError s!"constructor profile stores changed: {reprStr stores}")
  IO.println s!"CONSTRUCTOR_COMPILER_PROFILE_FORWARD_PASS: original checker1000/cache2/table2; one complete profile and automatic catalog; original nine operations and ordered nested payload; exact three issuance identities, six Dynamic execution outcomes, sufficient fuel for every output selection and later word outputs; new20/factory30export/old10/builtin37; stores {reprStr stores}"

end Tests.SourceCoreConstructorCalls.CompilerProfile
