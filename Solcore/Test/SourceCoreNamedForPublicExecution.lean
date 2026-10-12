import Solcore.Test.SourceCoreNamedForForward

/-! An independently checked and compiled named for executes one iteration
and then zero iterations through two public calls. Its real returned session carries the first
heap into the second call; each Source trace also entails sufficient public
execution and output fuel at that call's original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreNamedFor
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedFactory fixture)
    (stages : ObservedStages fixture observed) (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (first : RetainedState support sequence.initial.call.completion.session [])
      (second : RetainedState support sequence.next.completion.session []),
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        ⟨[]⟩ [.word firstInput, .word firstValue, .bool true, .bool false] (.value (.word firstValue)) first.heap ∧
      SourceCall support support.actual.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
        first.heap [.word secondInput, .word secondValue, .bool false, .bool false] (.value (.word secondInput)) second.heap ∧
      InitialForwardAt support sequence.initial first.heap ∧
      ForwardAt support sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed stages receiver.completion.result.context.registry receiver.issued
  obtain ⟨first, initialTrace⟩ := first_meaning support stages sequence.initial
  obtain ⟨second, nextTrace⟩ := first.update sequence.next
    (RecursiveStageRegistry.scope stages.sidecar [] support.actual.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have firstReady := sequence.initial.call.executed.exportsReady initialReady
  exact ⟨receiver, support, first, second, initialTrace, nextTrace,
    forward_initial support sequence.initial initialTrace,
    forward_update first sequence.next firstReady nextTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeFactory fixture
  let stages ← observeStages fixture observed
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed stages sequence
  IO.println "Actual named for: (11,12,true,false)->12 then (22,23,false,false)->22, exact Source histories and sufficient public fuel for both calls proved"

end Tests.SourceCoreNamedFor
