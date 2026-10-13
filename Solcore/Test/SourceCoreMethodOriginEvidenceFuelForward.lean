import Solcore.Test.SourceCoreMethodOriginEvidenceFuelFixture
import Solcore.Test.SourceCoreMethodOriginEvidenceSequenceForward

/-! The original checker receipt at its actual budget constructs the static
support consumed by all seven Source traces and public forward conclusions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

/-- Every support family is issued from the supplied original checker success. -/
theorem static_supports_at_checkfuel (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨program⟩ := admission.certificate.issue_for_checked fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.wordRow.entryMember
    given.rows (admission.aligned given) (by rw [fixture.sameProgram]; exact checked)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := given.distinct
    program := program }⟩

/-- Automatic catalog construction consumes the same actual checker receipt. -/
theorem ObservedProgramCertificate.automatic_catalog_at_checkfuel
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program) :
    ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
      Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
        (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        receiver.completion) := by
  exact admission.certificate.issue fixture.source_wellFormed fixture.recipePrepared receiver.issued
    receiver.registry observed.wordRow.entryMember (by rw [fixture.sameProgram]; exact checked)

theorem sequence_meaning_at_checkfuel {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports_at_checkfuel fixture observed admission receiver checked
  obtain ⟨firstEntry, firstType, firstHandle, initial, firstTrace⟩ := first_meaning_typed_handle
    support.toOrdinaryInventory support.distinct
    support.program wordStages sequence.first
  obtain ⟨second⟩ := RetainedState.bool_factory_meaning support initial false true true sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨firstRead⟩ := RetainedState.useWord_meaning support second.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.firstRead sequence.firstValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨third⟩ := RetainedState.word_factory_meaning support firstRead.after
    (Core.Word.ofNatModulo 55) (Core.Word.ofNatModulo 66) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨secondRead⟩ := RetainedState.useBool_meaning support third.after second.entry
    (by simp) second.entryType second.handleEq true sequence.secondRead sequence.secondValue useBoolStages
    (RecursiveStageRegistry.scope useBoolStages.sidecar [] support.useBoolHeader.header.function)
  obtain ⟨repeatedRead⟩ := RetainedState.useWord_meaning support secondRead.after firstEntry
    (by simp) firstType firstHandle (Core.Word.ofNatModulo 33) sequence.repeatedRead sequence.repeatedValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  obtain ⟨thirdRead⟩ := RetainedState.useWord_meaning support repeatedRead.after third.entry
    (by simp) third.entryType third.handleEq (Core.Word.ofNatModulo 55) sequence.thirdRead sequence.thirdValue useWordStages
    (RecursiveStageRegistry.scope useWordStages.sidecar [] support.useWordHeader.header.function)
  exact ⟨⟨support, firstEntry, firstType, firstHandle, initial, firstTrace,
    second, firstRead, third, secondRead, repeatedRead, thirdRead⟩⟩


/-- The seven-call witness and all seven forward bounds use the supplied budget. -/
theorem closed_sequence_forward_meaning_at_checkfuel
    (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    {checkingFuel : Nat} (checked : checkProgram workspace checkingFuel = .ok fixture.program)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver),
      ForwardMeaning meaning := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨meaning⟩ := sequence_meaning_at_checkfuel wordStages boolStages useWordStages useBoolStages
    admission checked sequence receiver
  exact ⟨receiver, meaning, meaning.forward⟩

/-- The concrete companion retains its method and all seven original conclusions. -/
theorem closed_sequence_forward_meaning_at1000
    (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (useWordStages : ObservedStages fixture observed.useWordRow.toObservedRow)
    (useBoolStages : ObservedStages fixture observed.useBoolRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (original : OriginalCheckAt1000 fixture)
    (sequence : ObservedSequence fixture observed) :
    fixture.program.methods.length = 1 ∧
      ∃ (receiver : ObservedReceiver fixture observed)
        (meaning : SequenceWitness wordStages boolStages useWordStages useBoolStages sequence receiver),
        ForwardMeaning meaning :=
  ⟨original.nonemptyMethods,
    closed_sequence_forward_meaning_at_checkfuel fixture observed wordStages boolStages useWordStages
      useBoolStages admission original.accepted sequence⟩

def runForwardAt1000 : IO Unit := do
  let fixture ← compiledFixture
  let ⟨original⟩ ← observeOriginalCheckAt1000 fixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let useWordStages ← observeStages fixture observed.useWordRow.toObservedRow
  let useBoolStages ← observeStages fixture observed.useBoolRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _automatic : ∃ receiver : ObservedReceiver fixture observed,
      ∃ catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog fixture.recipe.compiled,
        Nonempty (CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
          (headers catalog.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
          receiver.completion) := by
    obtain ⟨receiver⟩ := initial_receiver fixture observed
    exact ⟨receiver, admission.automatic_catalog_at_checkfuel receiver original.accepted⟩
  have _meaning := closed_sequence_forward_meaning_at1000 fixture observed wordStages boolStages
    useWordStages useBoolStages admission original sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [13,31,49,122,140,213,286,340] do
    throw (IO.userError s!"method scoped stores changed: {reprStr stores}")
  IO.println "METHOD_ORIGIN_EVIDENCE_FUEL_1000_PASS: original checker1000; selected method checker1024; one original method; seven Source calls and all seven public forward bounds; scalar33/true/33/55"

end Tests.SourceCoreMethodOriginEvidence
