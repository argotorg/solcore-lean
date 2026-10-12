import Solcore.Test.SourceCoreOperatorCallsForward
import Solcore.Test.SourceCoreOperatorCallsSeed

/-! The actual compiler emits a conditional containing two indirect calls and
Word arithmetic. The same genuinely issued identity handle is reused in both
selected branches, on the exact sessions returned by the previous executions.
Independent Source traces entail sufficient public fuel for both calls. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (identityStages : ObservedStages fixture observed.identityRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed) (support : PublicSupports receiver)
      (initial : RetainedState support sequence.initial.call.completion.session [])
      (entry : Entry) (issued : RetainedState support sequence.named.completion.session [entry])
      (first : RetainedState support sequence.first.completion.session [entry])
      (second : RetainedState support sequence.next.completion.session [entry]),
      entry.sourceType = functionType ∧ entry.handle = sequence.named.handle ∧
      issued.heap = initial.heap ∧
      SourceCall support support.identityHeader.header
        (RecursiveStageRegistry.scope identityStages.sidecar [] support.identityHeader.header.function)
        ⟨[]⟩ [.word seed] (.value (.word seed)) initial.heap ∧
      SourceCall support support.selectHeader.header
        (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
        issued.heap [entry.source, .bool false, .word firstValue] (.value (.word secondValue)) first.heap ∧
      SourceCall support support.selectHeader.header
        (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
        first.heap [entry.source, .bool true, .word secondValue] (.value (.word zero)) second.heap ∧
      ForwardAt support [entry] sequence.first first.heap ∧
      ForwardAt support [entry] sequence.next second.heap := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  obtain ⟨support⟩ := static_supports fixture observed identityStages selectStages
    receiver.completion.result.context.registry receiver.issued
  obtain ⟨initial, initialTrace⟩ := first_meaning support identityStages sequence.initial
  obtain ⟨entry, entryType, entryHandle, _handleType, _source, issued, sameHeap⟩ :=
    remember_named initial sequence.named
  have member : entry ∈ [entry] := .head _
  obtain ⟨first, firstTrace⟩ := issued.select entry member entryType entryHandle sequence.first
    (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
  obtain ⟨second, secondTrace⟩ := first.select entry member entryType entryHandle sequence.next
    (RecursiveStageRegistry.scope selectStages.sidecar [] support.selectHeader.header.function)
  have initialReady : sequence.initial.session.ExportsReady :=
    (show sequence.initial.bootstrap.ReadyAt 100000 sequence.initial.session from .single sequence.initial.ready).exportsReady
      sequence.initial.authority
  have seededReady := sequence.initial.call.executed.exportsReady initialReady
  have issuedReady := sequence.named.issued.exportsReady seededReady
  have firstReady := sequence.first.executed.exportsReady issuedReady
  exact ⟨receiver, support, initial, entry, issued, first, second, entryType, entryHandle,
    sameHeap, initialTrace, firstTrace, secondTrace,
    forward_select issued entry member entryType entryHandle sequence.first issuedReady firstTrace,
    forward_select first entry member entryType entryHandle sequence.next firstReady secondTrace⟩

def run : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let identityStages ← observeStages fixture observed.identityRow
  let selectStages ← observeStages fixture observed.selectRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_sequence_meaning fixture observed identityStages selectStages sequence
  IO.println "Actual indirect identity calls under unary/conditional/Word operators: false11→22 then true22→0; same handle, exact Source histories, sufficient public fuel"

end Tests.SourceCoreOperatorCalls
