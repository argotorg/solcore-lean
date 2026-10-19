import Solcore.Test.SourceCoreGeneralizedExportHistory

/-! Factory and unrelated named calls preserve the earlier exported instances
and the exact saved Source cell across their real public completions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (StartedCall)

variable {observed : Observed} {context : Context observed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle : SourceCorePublicValues.Handle} {seed : Word}

structure CapturePlan (history : PairHistory context session wordHandle boolHandle) (seed : Word)
    (call : StartedCall session observed.capture.original.key [.word seed] runOptions) where
  selected : SelectedInventory context.whole observed.capture
  plan : NextSourcePlan context.first history.retained selected [.word seed] [.word seed] call
    ((selected.capture_shape observed.captureShape).value selected.packet.header.context
      (inputEnvironment (selected.capture_shape observed.captureShape).principal.input history.retained.state.heap)
      selected.packet.header.function.evidence)
    ((selected.capture_shape observed.captureShape).principal.allocatedHeap selected.packet.header.context
      (inputEnvironment (selected.capture_shape observed.captureShape).principal.input history.retained.state.heap)
      (inputHeap history.retained.state.heap .word (.word seed)))

theorem PairHistory.plan_capture (history : PairHistory context session wordHandle boolHandle) (seed : Word)
    (call : StartedCall session observed.capture.original.key [.word seed] runOptions) :
    Nonempty (CapturePlan history seed call) := by
  obtain ⟨selected⟩ := context.whole.select observed.capture
  obtain ⟨plan⟩ := capture_plan context.first history.retained selected observed.captureShape seed observed.typing call
  exact ⟨⟨selected,plan⟩⟩

theorem CapturePlan.collected {history : PairHistory context session wordHandle boolHandle}
    {call : StartedCall session observed.capture.original.key [.word seed] runOptions}
    (planned : CapturePlan history seed call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned))
    (valueEq : returned.value = .function captureHandle) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  let selected := planned.selected
  let shape := selected.capture_shape observed.captureShape
  let environment := inputEnvironment shape.principal.input history.retained.state.heap
  let selection : RecursiveNamedPublicOutputSelections.Selection selected.packet.header.function.resultType returned.value :=
    functionSelection valueEq
  obtain ⟨added,continued,payload,_handles,selectedLeaf,heapEq,maps,worlds,materialized⟩ :=
    planned.plan.observed_materialized context.first history.retained selected observed.typing
      observed.captureProfile resumed selection
  have addedEq := function_selected valueEq selectedLeaf
  subst added
  let entry : Entry := ⟨selected.packet.header.function.resultType,
    shape.value selected.packet.header.context environment selected.packet.header.function.evidence,
    captureHandle,payload,selected.packet.header.output,outputFuel⟩
  have allocated : Dynamic.Heap.Allocates history.retained.state.heap .word (some (.word seed))
      ⟨history.retained.state.heap.cells.length⟩ (inputHeap history.retained.state.heap .word (.word seed)) := .append
  have generalized : Dynamic.Heap.AllocatesGeneralized (inputHeap history.retained.state.heap .word (.word seed))
      (shape.principal.descriptor selected.packet.header.context environment)
      ⟨(inputHeap history.retained.state.heap .word (.word seed)).cells.length⟩
      (shape.principal.allocatedHeap selected.packet.header.context environment
        (inputHeap history.retained.state.heap .word (.word seed))) := .append
  have read := generalized.preserves_read allocated.reads_new
  refine ⟨⟨⟨_,continued,(history.origins.extend maps worlds).append
    (CellAwareMaterializedRetainedEntries.Retained.of_selected (owner observed.fixture.original.recipe.compiled) materialized),
    history.wordEntry.append [entry],history.boolEntry.append [entry]⟩,?_⟩⟩
  exact ⟨entry,List.mem_append_right _ List.mem_cons_self,rfl,selected.result_eq.trans observed.captureResult,
    _,shape,selected.packet.header.context,environment,[(shape.principal.typeVariable,.bool)],
    selected.packet.header.function.evidence.applySubstitution [(shape.principal.typeVariable,.bool)],rfl,
    ⟨history.retained.state.heap.cells.length⟩,.head,heapEq.symm ▸ read⟩

structure TickPlan (history : FullHistory context session wordHandle boolHandle captureHandle seed) (flag : Bool)
    (call : StartedCall session observed.tick.original.key [.bool flag] runOptions) where
  selected : SelectedInventory context.whole observed.tick
  plan : NextSourcePlan context.first history.pair.retained selected [.bool flag] [.bool flag] call
    (.bool flag) (inputHeap history.pair.retained.state.heap .bool (.bool flag))

theorem FullHistory.plan_tick (history : FullHistory context session wordHandle boolHandle captureHandle seed) (flag : Bool)
    (call : StartedCall session observed.tick.original.key [.bool flag] runOptions) :
    Nonempty (TickPlan history flag call) := by
  obtain ⟨selected⟩ := context.whole.select observed.tick
  obtain ⟨plan⟩ := tick_plan context.first history.pair.retained selected observed.tickShape flag observed.typing call
  exact ⟨⟨selected,plan⟩⟩

theorem TickPlan.retained {history : FullHistory context session wordHandle boolHandle captureHandle seed}
    {flag : Bool} {call : StartedCall session observed.tick.original.key [.bool flag] runOptions}
    (planned : TickPlan history flag call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  obtain ⟨added,continued,payload,_handles,selectedLeaf,heapEq,maps,worlds⟩ :=
    planned.plan.observed_collected context.first history.pair.retained planned.selected observed.typing resumed .skip
  have addedEq := skip_selected selectedLeaf
  subst added
  have allocated : Dynamic.Heap.Allocates history.pair.retained.state.heap .bool (some (.bool flag))
      ⟨history.pair.retained.state.heap.cells.length⟩ (inputHeap history.pair.retained.state.heap .bool (.bool flag)) := .append
  refine ⟨⟨⟨_,continued,(history.pair.origins.extend maps worlds).append .nil,
    history.pair.wordEntry.append [],history.pair.boolEntry.append []⟩,?_⟩⟩
  exact { history.captured with
    member := List.mem_append_left [] history.captured.member
    read := heapEq.symm ▸ allocated.preserves_read history.captured.read }

end Tests.SourceCoreGeneralizedExport
