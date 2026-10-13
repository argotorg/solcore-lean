import Solcore.Test.SourceCoreEvidenceMethodInitialForward
import Solcore.Test.SourceCoreEvidenceMethodPublicExecution

/-! The actual four-call method program closes both directions through the
same physical family. Every call retains its Source heap and obtains sufficient
execution and output fuel at its original public checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {before : RetainedState support.toOrdinaryInventory receiver session []}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments scalar.publicValue}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (bodies : MethodBodies fixture)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    ForwardAt (entries := []) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs simple meaning.rawType meaning.nativeType ready
    (support.terminals meaning.request.header meaning.request.selected.member)
    (fun budget {child} selected => preserves_bodies receiver support bodies before.issued before.extension
      meaning.request.header meaning.request.selected.member selected budget)
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.initial.heap
  second : ForwardAt (entries := []) meaning.support.toOrdinaryInventory receiver (.bool false)
    sequence.second meaning.secondMeaning.after.heap
  third : ForwardAt (entries := []) meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 33))
    sequence.third meaning.thirdMeaning.after.heap
  fourth : ForwardAt (entries := []) meaning.support.toOrdinaryInventory receiver (.bool true)
    sequence.fourth meaning.fourthMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver)
    (bodies : MethodBodies fixture) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have thirdReady := sequence.third.executed.exportsReady secondReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      (meaning.support.terminals meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member)
      (fun budget {child} selected => preserves_bodies receiver meaning.support bodies receiver.issued (.refl _)
        meaning.support.wordHeader.header meaning.support.toOrdinaryInventory.word_member selected budget)
      meaning.firstTrace,
    meaning.secondMeaning.forward bodies (bool_simple false) firstReady,
    meaning.thirdMeaning.forward bodies (word_simple (Core.Word.ofNatModulo 33)) secondReady,
    meaning.fourthMeaning.forward bodies (bool_simple true) thirdReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (bodies : MethodBodies fixture)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages methods bodies sequence
  exact ⟨receiver, meaning, meaning.forward bodies⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let ⟨methods⟩ ← observeMethodCatalog fixture
  let ⟨bodies⟩ ← observeMethodBodies fixture
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_forward_meaning fixture observed wordStages boolStages methods bodies sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.third.completion.session.heapSize,
    sequence.fourth.completion.session.heapSize]
  unless stores == [7, 16, 25, 34, 43] do
    throw (IO.userError s!"method session stores changed: {reprStr stores}")
  IO.println "EVIDENCE_METHOD_FORWARD_PASS: Word11, BoolFalse, Word33, BoolTrue; four Source histories and sufficient public fuel; stores7/16/25/34/43"

end Tests.SourceCoreEvidenceMethod
