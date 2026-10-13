import Solcore.Test.SourceCoreCoercionPublicInitialForward
import Solcore.Test.SourceCoreCoercionPublicFactoryForward
import Solcore.Test.SourceCoreCoercionPublicForward
import Solcore.Test.SourceCoreCoercionPublicPublicExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCoercionPublic
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (ready : session.ExportsReady) :
    ForwardAt (entries := entries) support.toOrdinaryInventory receiver scalar call meaning.after.heap := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support
  apply forward_call before scalar call meaning.request meaning.inputs meaning.registry meaning.rawType meaning.nativeType ready
    program
  rw [meaning.headerEq]
  exact meaning.trace

theorem FactoryMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    {support : StaticSupportPackage fixture observed receiver.completion}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry}
    {before : RetainedState support.toOrdinaryInventory receiver session entries}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session key publicArguments} {resultType : TypeSystem.Ty}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : FactoryMeaning before header call resultType arguments invocation)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (ready : session.ExportsReady) :
    FactoryForwardAt (entries := entries) support.toOrdinaryInventory receiver call resultType meaning.entry.source meaning.after.heap := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver support
  apply forward_factory before call meaning.request meaning.inputs simple meaning.rawType ready
    program
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow.toObservedRow}
    {useStages : ObservedStages fixture observed.useRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages useStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support.toOrdinaryInventory receiver sequence.first meaning.firstEntry.source meaning.initial.heap
  second : FactoryForwardAt (entries := [meaning.firstEntry]) meaning.support.toOrdinaryInventory receiver sequence.second .word
    meaning.secondMeaning.entry.source meaning.secondMeaning.after.heap
  firstRead : ForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 41)) sequence.firstRead meaning.firstReadMeaning.after.heap
  third : FactoryForwardAt (entries := [meaning.firstEntry] ++ [meaning.secondMeaning.entry]) meaning.support.toOrdinaryInventory receiver
    sequence.third .word meaning.thirdMeaning.entry.source meaning.thirdMeaning.after.heap
  secondRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 7)) sequence.secondRead meaning.secondReadMeaning.after.heap
  repeatedRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 41)) sequence.repeatedRead meaning.repeatedReadMeaning.after.heap
  thirdRead : ForwardAt (entries := ([meaning.firstEntry] ++ [meaning.secondMeaning.entry]) ++ [meaning.thirdMeaning.entry])
    meaning.support.toOrdinaryInventory receiver (.word (Core.Word.ofNatModulo 7)) sequence.thirdRead meaning.thirdReadMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {makeStages : ObservedStages fixture observed.makeRow.toObservedRow}
    {useStages : ObservedStages fixture observed.useRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness makeStages useStages sequence receiver)
    : ForwardMeaning meaning := by
  obtain ⟨program⟩ := StaticSupportPackage.program_support receiver meaning.support
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 102400 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have firstReadReady := sequence.firstRead.executed.exportsReady secondReady
  have thirdReady := sequence.third.executed.exportsReady firstReadReady
  have secondReadReady := sequence.secondRead.executed.exportsReady thirdReady
  have repeatedReady := sequence.repeatedRead.executed.exportsReady secondReadReady
  exact ⟨forward_initial meaning.support.toOrdinaryInventory meaning.support.distinct sequence.first
      program
      meaning.firstTrace,
    meaning.secondMeaning.forward (bool_simple false) firstReady,
    meaning.firstReadMeaning.forward secondReady,
    meaning.thirdMeaning.forward (bool_simple false) firstReadReady,
    meaning.secondReadMeaning.forward thirdReady,
    meaning.repeatedReadMeaning.forward secondReadReady,
    meaning.thirdReadMeaning.forward repeatedReady⟩

theorem closed_sequence_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow.toObservedRow)
    (useStages : ObservedStages fixture observed.useRow.toObservedRow)
    (admission : ObservedProgramCertificate fixture observed)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness makeStages useStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed makeStages useStages
    admission sequence
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let admission ← observeProgramCertificate fixture observed
  let makeStages ← observeStages fixture observed.makeRow.toObservedRow
  let useStages ← observeStages fixture observed.useRow.toObservedRow
  let sequence ← observeSequence fixture observed
  have _automatic := admission.automatic_catalog_initial
  have _meaning := closed_sequence_forward_meaning fixture observed makeStages useStages
    admission sequence
  let stores := [sequence.first.session.heapSize, sequence.first.completion.session.heapSize,
    sequence.second.completion.session.heapSize, sequence.firstRead.completion.session.heapSize,
    sequence.third.completion.session.heapSize, sequence.secondRead.completion.session.heapSize,
    sequence.repeatedRead.completion.session.heapSize, sequence.thirdRead.completion.session.heapSize]
  unless stores == [5,8,11,20,23,32,41,50] do
    throw (IO.userError s!"coercion public stores changed: {reprStr stores}")
  IO.println "COERCION_PUBLIC_FORWARD_PASS: seven Source calls; all seven sufficient public fuel bounds; three retained closures; scalar41/7/41/7; original constrained direct call and Bool-to-Word coercion"

end Tests.SourceCoreCoercionPublic
