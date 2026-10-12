import Solcore.Test.SourceCoreConstructorCallsInvocation
import Solcore.Test.SourceCoreConstructorCallsCollection
import Solcore.Test.SourceCoreConstructorCallsSeed

/-! The actual constructor creates a fresh capture by an indirect child call,
exports it beside three existing callable kinds, and reuses the selected
handles through the exact subsequent sessions and Source heaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  first : Entry
  factory : Entry
  builtin : Entry
  named : Entry
  firstType : first.sourceType = closureType
  factoryType : factory.sourceType = makerType
  builtinType : builtin.sourceType = convertType
  namedType : named.sourceType = .function packedType (containerType fixture.dataType)
  firstHandle : first.handle = sequence.first.handle
  factoryHandle : factory.handle = sequence.factory.handle
  builtinHandle : builtin.handle = sequence.builtin.handle
  namedHandle : named.handle = sequence.named.handle
  source : Dynamic.Value
  added : List Entry
  collected : Collected observed source sequence.construction.newOutput sequence.construction.priorOutput
    sequence.construction.factoryOutput sequence.construction.builtinOutput added
  initial : RetainedState support sequence.first.completion.session [first]
  issuedState : RetainedState support sequence.named.completion.session [first, factory, builtin, named]
  collectedState : RetainedState support sequence.construction.completion.session ([first, factory, builtin, named] ++ added)
  newReadState : RetainedState support sequence.newRead.completion.session ([first, factory, builtin, named] ++ added)
  interveningState : RetainedState support sequence.intervening.completion.session ([first, factory, builtin, named] ++ added)
  priorReadState : RetainedState support sequence.priorRead.completion.session ([first, factory, builtin, named] ++ added)
  finalState : RetainedState support sequence.builtinRead.completion.session ([first, factory, builtin, named] ++ added)
  firstTrace : SourceCall support support.makeHeader.header
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    ⟨[]⟩ [.word seed] (.value first.source) initial.heap
  issuedHeap : issuedState.heap = initial.heap
  constructionTrace : SourceConstruction support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    issuedState.heap named.source factory.source first.source builtin.source source collectedState.heap
  newArguments : List Dynamic.Value
  newPacking : Dynamic.ValuesPack newArguments .unit
  newReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    collectedState.heap collected.newEntry.source newArguments (.value (.word secondSeed)) newReadState.heap
  interveningArguments : List Dynamic.Value
  interveningPacking : Dynamic.ValuesPack interveningArguments (.word interveningSeed)
  interveningSource : Dynamic.Value
  interveningTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    newReadState.heap collected.factoryEntry.source interveningArguments (.value interveningSource) interveningState.heap
  priorArguments : List Dynamic.Value
  priorPacking : Dynamic.ValuesPack priorArguments .unit
  priorReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    interveningState.heap collected.priorEntry.source priorArguments (.value (.word seed)) priorReadState.heap
  builtinArguments : List Dynamic.Value
  builtinPacking : Dynamic.ValuesPack builtinArguments (.integer 37)
  builtinReadTrace : SourceInvocation support
    (RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function)
    priorReadState.heap collected.builtinEntry.source builtinArguments (.value (.word (Core.Word.ofNatModulo 37))) finalState.heap

theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness makeStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports (completion := receiver.completion)
    fixture observed extra makeStages readStages receiver.completion.result.context.registry receiver.issued
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, _firstHandleType, initial, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨factory, factoryType, factoryHandle, _factoryHandleType, _factorySource, factoryState, factoryHeap⟩ :=
    remember_maker initial sequence.factory
  obtain ⟨builtin, builtinType, builtinHandle, _builtinHandleType, _builtinSource, builtinState, builtinHeap⟩ :=
    remember_builtin factoryState sequence.builtin
  obtain ⟨named, namedType, namedHandle, _namedHandleType, _namedSource, issuedState, issuedHeap⟩ :=
    remember_named builtinState sequence.named
  obtain ⟨source, added, collected, collectedState, constructionTrace⟩ :=
    collect issuedState named factory first builtin (by simp) (by simp) (by simp) (by simp)
      namedType factoryType firstType builtinType namedHandle factoryHandle firstHandle builtinHandle
      sequence.construction scope
  have newMember : collected.newEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have priorMember : collected.priorEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have factoryMember : collected.factoryEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have builtinMember : collected.builtinEntry ∈ [first, factory, builtin, named] ++ added := by simp [collected.ordered]
  have unitInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      ([first, factory, builtin, named] ++ added) support.makeHeader.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have wordInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      ([first, factory, builtin, named] ++ added) support.makeHeader.header.function.context
      .word (.word interveningSeed) (.word interveningSeed) :=
    .data ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
      ⟨.word interveningSeed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word interveningSeed⟩
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input
      ([first, factory, builtin, named] ++ added) support.makeHeader.header.function.context
      .integer (.integer 37) (.integer 37) :=
    .data ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
      ⟨.integer 37, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer 37⟩
  obtain ⟨newArguments, newReadState, newPacking, newReadTrace⟩ := invoke_word collectedState collected.newEntry
    newMember collected.newType collected.newHandle sequence.construction.newType unitInput
    sequence.newRead sequence.newValue scope
  obtain ⟨interveningArguments, interveningSource, interveningState, interveningPacking, interveningTrace⟩ :=
    invoke_success newReadState collected.factoryEntry factoryMember collected.factoryType collected.factoryHandle
      wordInput sequence.intervening scope
  obtain ⟨priorArguments, priorReadState, priorPacking, priorReadTrace⟩ := invoke_word interveningState collected.priorEntry
    priorMember collected.priorType collected.priorHandle sequence.construction.priorType unitInput
    sequence.priorRead sequence.priorValue scope
  obtain ⟨builtinArguments, finalState, builtinPacking, builtinReadTrace⟩ := invoke_word priorReadState collected.builtinEntry
    builtinMember collected.builtinType collected.builtinHandle sequence.construction.builtinType integerInput
    sequence.builtinRead sequence.builtinValue scope
  exact ⟨{
    support := support
    first := first
    factory := factory
    builtin := builtin
    named := named
    firstType := firstType
    factoryType := factoryType
    builtinType := builtinType
    namedType := namedType
    firstHandle := firstHandle
    factoryHandle := factoryHandle
    builtinHandle := builtinHandle
    namedHandle := namedHandle
    source := source
    added := added
    collected := collected
    initial := initial
    issuedState := issuedState
    collectedState := collectedState
    newReadState := newReadState
    interveningState := interveningState
    priorReadState := priorReadState
    finalState := finalState
    firstTrace := firstTrace
    issuedHeap := issuedHeap.trans (builtinHeap.trans factoryHeap)
    constructionTrace := constructionTrace
    newArguments := newArguments
    newPacking := newPacking
    newReadTrace := newReadTrace
    interveningArguments := interveningArguments
    interveningPacking := interveningPacking
    interveningSource := interveningSource
    interveningTrace := interveningTrace
    priorArguments := priorArguments
    priorPacking := priorPacking
    priorReadTrace := priorReadTrace
    builtinArguments := builtinArguments
    builtinPacking := builtinPacking
    builtinReadTrace := builtinReadTrace
  }⟩

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
  IO.println "Constructor with indirect child: new capture20, retained factory30, old capture10, builtin37; exact Source traces, ordered collected payloads and returned histories proved"

end Tests.SourceCoreConstructorCalls
