import Solcore.Test.SourceCoreCapturedLocalInvocation
import Solcore.Test.SourceCoreCapturedLocalSeed

/-! Actual make(10) initializes a lexical local and exports a closure over that
cell. Two direct calls consume the original handle and each current returned
session, with independent Source applications and complete retained histories. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) where
  factory : ObservedPublicRun fixture observed
  first : ObservedInvocation factory.completion.session factory.handle
  second : ObservedInvocation first.completion.session factory.handle

def observeSequence (fixture : CompiledFixture) (observed : ObservedFactory fixture) :
    IO (ObservedSequence fixture observed) := do
  let factory ← observePublicRun fixture observed
  let first ← observeInvocation factory.completion.session factory.handle
  let second ← observeInvocation first.completion.session factory.handle
  return ⟨factory, first, second⟩

def SequenceMeaning {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) : Prop :=
  ∃ support : PublicSupports receiver,
    let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
    ∃ (entry : Entry) (function : Dynamic.Closure),
      entry.sourceType = .function .unit .word ∧ entry.handle = sequence.factory.handle ∧
      entry.source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word ∧
      BinderExtends support.actual.header.function.source.owner support.actual.header.context
        observed.localBinder function.context ∧
      ∃ initial : RetainedState support sequence.factory.completion.session [entry],
      ∃ first : RetainedState support sequence.first.completion.session [entry],
      ∃ final : RetainedState support sequence.second.completion.session [entry],
        (∃ location, Dynamic.Environment.LooksUp function.captured observed.localBinder.id location ∧
          Dynamic.Heap.Reads initial.heap location { type := .word, value := some (.word seed) }) ∧
        SourceCall support support.actual.header scope ⟨[]⟩ [.word seed] (.value entry.source) initial.heap ∧
        SourceInvocation support scope initial.heap entry.source (.value (.word seed)) first.heap ∧
        SourceInvocation support scope first.heap entry.source (.value (.word seed)) final.heap

/-- The static lexical tree and closure family come from the actual accepted
program. The factory allocation and both direct calls share one retained history. -/
theorem sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    SequenceMeaning stages sequence receiver := by
  obtain ⟨support⟩ := static_supports
    (completion := CallableIndexedOwnedPublicFaultReceivers.Receiver.of_completion receiver.completion) fixture observed stages receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicFaultReceiverTables.issued_of_runSource receiver.executed)
  let scope := RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function
  obtain ⟨entry, entryType, handle, handleType, initial, factoryTrace⟩ :=
    first_meaning support stages sequence.factory
  obtain ⟨function, source, parameters, result, extended, location, capture, cell⟩ := factoryTrace.make_capture
  obtain ⟨first, firstTrace⟩ := invoke initial entry (by simp) entryType source parameters handle handleType
    sequence.first sequence.first.returned scope
  obtain ⟨final, finalTrace⟩ := invoke first entry (by simp) entryType source parameters handle handleType
    sequence.second sequence.second.returned scope
  exact ⟨support, entry, function, entryType, handle, source, parameters, result, extended,
    initial, first, final, ⟨location, capture, cell⟩, factoryTrace, firstTrace, finalTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  let receiver ← observeReceiver fixture observed
  have _meaning := sequence_meaning fixture observed stages sequence receiver
  IO.println "Actual lexical capture: initialized local, repeated results 10/10, Source applications and returned histories proved"

end Tests.SourceCoreCapturedLocal
