import Solcore.Test.SourceCoreCapturedNestedInvocation
import Solcore.Test.SourceCoreCapturedNestedCollection
import Solcore.Test.SourceCoreCapturedNestedSeed
import Solcore.Test.SourceCoreCapturedNestedMakeStep
import Solcore.Test.SourceCoreCapturedNestedClosureShape

/-! A closed seven-call sequence collects multiple distinct captures from an
ordered mapping output and then uses the collected entries across another
factory call. Duplicate keys and repeated aliases remain separate occurrences. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCapturedNested
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  second : Entry
  named : Entry
  intervening : Entry
  namedType : named.sourceType = .function containerType containerType
  namedHandle : named.handle = sequence.named.handle
  namedSource : named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
    support.readPacket.header.named.specialized support.readInput.prepared.available))
  firstType : first.sourceType = .function .unit .word
  secondType : second.sourceType = .function .unit .word
  firstHandle : first.handle = sequence.first.handle
  secondHandle : second.handle = sequence.second.handle
  firstHandleType : sequence.first.handle.sourceType = .function .unit .word
  secondHandleType : sequence.second.handle.sourceType = .function .unit .word
  distinct : first.handle ≠ second.handle
  added : List Entry
  collected : Collected first.source second.source sequence.echo.firstOutput sequence.echo.secondOutput
    sequence.echo.repeatedOutput added
  initial : RetainedState support sequence.first.completion.session [first]
  secondState : RetainedState support sequence.second.completion.session [first, second]
  issuedState : RetainedState support sequence.named.completion.session [first, second, named]
  collectedState : RetainedState support sequence.echo.completion.session ([first, second, named] ++ added)
  firstReadState : RetainedState support sequence.firstRead.completion.session ([first, second, named] ++ added)
  interveningState : RetainedState support sequence.intervening.completion.session
    (([first, second, named] ++ added) ++ [intervening])
  secondReadState : RetainedState support sequence.secondRead.completion.session
    (([first, second, named] ++ added) ++ [intervening])
  finalState : RetainedState support sequence.repeatedRead.completion.session
    (([first, second, named] ++ added) ++ [intervening])
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  secondTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    initial.heap [.word secondSeed] (.value second.source) secondState.heap
  issuedHeap : issuedState.heap = secondState.heap
  echoTrace : SourceCall support support.readHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    issuedState.heap [sourceArgument first.source second.source]
    (.value (sourceArgument first.source second.source)) collectedState.heap
  codec : CollectedAt (fixture := fixture) sequence.echo.completion sequence.echo.firstOutput
    sequence.echo.secondOutput sequence.echo.repeatedOutput sequence.echo.returned
    (sourceArgument first.source second.source) added
  firstReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    collectedState.heap collected.firstEntry.source (.value (.word seed)) firstReadState.heap
  interveningTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    firstReadState.heap [.word interveningSeed] (.value intervening.source) interveningState.heap
  secondReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    interveningState.heap collected.secondEntry.source (.value (.word secondSeed)) secondReadState.heap
  repeatedReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    secondReadState.heap collected.repeatedEntry.source (.value (.word seed)) finalState.heap

/-- All semantic premises come from the actual accepted program, public
receipts and retained compiler certificates. No body execution law is supplied. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra makeStages readStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨second, secondType, secondHandle, secondHandleType, secondState, secondTrace⟩ :=
    initial.make_typed_handle extra sequence.second scope
  obtain ⟨secondClosure, secondSource, secondParameters, _secondResult⟩ := secondTrace.make_closure
  obtain ⟨named, namedType, namedHandle, _namedHandleType, namedSource, issuedState, issuedHeap⟩ :=
    remember_named secondState sequence.named
  obtain ⟨added, collected, collectedState, echoTrace, codec⟩ := collect issuedState named first second
    (by simp) (by simp) (by simp) namedType firstType secondType namedSource namedHandle firstHandle secondHandle
    sequence.echo scope
  have firstMember : collected.firstEntry ∈ [first, second, named] ++ added := by
    simp [collected.ordered]
  have secondMember : collected.secondEntry ∈ ([first, second, named] ++ added) := by
    simp [collected.ordered]
  have repeatedMember : collected.repeatedEntry ∈ ([first, second, named] ++ added) := by
    simp [collected.ordered]
  have firstOutputType : sequence.echo.firstOutput.sourceType = .function .unit .word :=
    (congrArg SourceCorePublicValues.Handle.sourceType sequence.echo.firstSame).trans firstHandleType
  have secondOutputType : sequence.echo.secondOutput.sourceType = .function .unit .word :=
    (congrArg SourceCorePublicValues.Handle.sourceType sequence.echo.secondSame).trans secondHandleType
  have repeatedOutputType : sequence.echo.repeatedOutput.sourceType = .function .unit .word :=
    (congrArg SourceCorePublicValues.Handle.sourceType sequence.echo.repeatedSame).trans firstHandleType
  obtain ⟨firstReadState, firstReadTrace⟩ := invoke collectedState collected.firstEntry firstMember
    collected.firstType collected.firstHandle firstOutputType (collected.firstSource.trans firstSource)
    firstParameters sequence.firstRead sequence.firstValue scope
  obtain ⟨intervening, _interveningType, _interveningHandle, _interveningHandleType, interveningState, interveningTrace⟩ :=
    firstReadState.make_typed_handle extra sequence.intervening scope
  obtain ⟨secondReadState, secondReadTrace⟩ := invoke interveningState collected.secondEntry
    (List.mem_append_left _ secondMember) collected.secondType collected.secondHandle secondOutputType
    (collected.secondSource.trans secondSource) secondParameters sequence.secondRead sequence.secondValue scope
  obtain ⟨finalState, repeatedReadTrace⟩ := invoke secondReadState collected.repeatedEntry
    (List.mem_append_left _ repeatedMember) collected.repeatedType collected.repeatedHandle repeatedOutputType
    (collected.repeatedSource.trans firstSource) firstParameters sequence.repeatedRead sequence.repeatedValue scope
  exact ⟨{
    support := support
    first := first
    second := second
    named := named
    intervening := intervening
    namedType := namedType
    namedHandle := namedHandle
    namedSource := namedSource
    firstType := firstType
    secondType := secondType
    firstHandle := firstHandle
    secondHandle := secondHandle
    firstHandleType := firstHandleType
    secondHandleType := secondHandleType
    distinct := by rw [firstHandle, secondHandle]; exact sequence.distinct
    added := added
    collected := collected
    initial := initial
    secondState := secondState
    issuedState := issuedState
    collectedState := collectedState
    firstReadState := firstReadState
    interveningState := interveningState
    secondReadState := secondReadState
    finalState := finalState
    firstTrace := firstTrace
    secondTrace := secondTrace
    issuedHeap := issuedHeap
    echoTrace := echoTrace
    codec := codec
    firstReadTrace := firstReadTrace
    interveningTrace := interveningTrace
    secondReadTrace := secondReadTrace
    repeatedReadTrace := repeatedReadTrace }⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed, Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning fixture observed extra makeStages readStages sequence receiver⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed extra makeStages readStages sequence
  IO.println "Nested output collection: ordered duplicate mapping rows, distinct captured handles, Source results 10/20/10 and actual returned histories proved"

end Tests.SourceCoreCapturedNested
