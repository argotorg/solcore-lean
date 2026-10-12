import Solcore.Test.SourceCoreDirectIssuedInvocation
import Solcore.Test.SourceCoreCapturedReuseSeed
import Solcore.Test.SourceCoreCapturedReuseClosureShape

/-! Actual named and builtin public invocation is connected to independent
Source execution across the same reached session and retained function history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreDirectIssued
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreCapturedReuse
open RecursiveNamedPublicFunctionHistory (Entry)

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (makeStages : ObservedStages fixture observed.makeRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
    ∃ first named builtin : Entry,
      first.sourceType = .function .unit .word ∧
      named.sourceType = .function (.function .unit .word) .word ∧
      builtin.sourceType = .function .integer .word ∧
      first.handle = sequence.first.handle ∧ named.handle = sequence.named.handle ∧
      builtin.handle = sequence.builtin.handle ∧
      named.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.readPacket.header.named.specialized support.readInput.prepared.available)) ∧
      builtin.source = .builtin ⟨.wordFromInteger⟩ ∧
      ∃ firstState : RetainedState support sequence.first.completion.session [first],
      ∃ namedState : RetainedState support sequence.named.completion.session [first, named],
      ∃ readState : RetainedState support sequence.read.completion.session [first, named],
      ∃ builtinState : RetainedState support sequence.builtin.completion.session [first, named, builtin],
      ∃ finalState : RetainedState support sequence.converted.completion.session [first, named, builtin],
        namedState.heap = firstState.heap ∧ builtinState.heap = readState.heap ∧
        SourceCall support support.makeHeader.header scope ⟨[]⟩ [.word seed] (.value first.source) firstState.heap ∧
        SourceInvocation support scope namedState.heap named.source first.source seed readState.heap ∧
        SourceInvocation support scope builtinState.heap builtin.source (.integer builtinArgument)
          builtinResult finalState.heap

/-- The compiler/checker observations and the actual IO calls discharge every
static, input, capture and public continuation premise for this sequence. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning makeStages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed extra makeStages readStages
    receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope makeStages.sidecar [] support.makeHeader.header.function
  obtain ⟨first, firstType, firstHandle, _firstHandleType, firstState, firstTrace⟩ :=
    first_meaning_typed_handle extra support makeStages sequence.first
  obtain ⟨firstClosure, firstSource, _firstParameters, _firstResult⟩ := firstTrace.make_closure
  obtain ⟨named, namedType, namedHandle, namedHandleType, namedSource, namedState, namedHeap⟩ :=
    remember_named firstState sequence.named
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named]
      support.makeHeader.header.function.context (.function .unit .word)
      (.function sequence.first.handle) first.source := by
    simpa only [firstType, firstHandle] using
      (RecursiveNamedPublicFunctionHistoryInputs.Input.retained
        (context := support.makeHeader.header.function.context) first (by simp : first ∈ [first, named]))
  obtain ⟨readState, readTrace⟩ := invoke namedState named (by simp) namedType namedHandle namedHandleType
    input (.function sequence.first.handle)
    (by intro sources packing; rw [firstSource] at packing ⊢; cases packing; rfl)
    sequence.read sequence.readValue scope
  obtain ⟨builtin, builtinType, builtinHandle, builtinHandleType, builtinSource, builtinState, builtinHeap⟩ :=
    remember_builtin readState sequence.builtin
  have integerInput : RecursiveNamedPublicFunctionHistoryInputs.Input [first, named, builtin]
      support.makeHeader.header.function.context .integer (.integer builtinArgument) (.integer builtinArgument) :=
    .data ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
      ⟨.integer builtinArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer builtinArgument⟩
  obtain ⟨finalState, finalTrace⟩ := invoke builtinState builtin (by simp) builtinType builtinHandle builtinHandleType
    integerInput (.simple (.integer builtinArgument))
    (by intro sources packing; cases packing; rfl) sequence.converted sequence.convertedValue scope
  exact ⟨support, first, named, builtin, firstType, namedType, builtinType,
    firstHandle, namedHandle, builtinHandle, namedSource, builtinSource,
    firstState, namedState, readState, builtinState, finalState, namedHeap, builtinHeap,
    firstTrace, readTrace, finalTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let extra ← observeMake fixture observed
  let makeStages ← observeStages fixture observed.makeRow
  let readStages ← observeStages fixture observed.readRow
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed extra makeStages readStages sequence receiver
  IO.println "Actual direct issued calls: named read of captured 10 and builtin conversion 37, Source arguments/results and current histories proved"

end Tests.SourceCoreDirectIssued
