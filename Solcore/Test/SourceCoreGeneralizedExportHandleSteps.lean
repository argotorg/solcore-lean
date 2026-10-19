import Solcore.Test.SourceCoreGeneralizedExportNamedSteps

/-! Each concrete retained handle receives its own Source call plan. Actual
returned sessions keep all earlier entries and the saved capture cell. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreGeneralizedExport
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open CellAwarePublicHandleStart (StartedCall)

variable {observed : Observed} {context : Context observed}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {wordHandle boolHandle captureHandle handle : SourceCorePublicValues.Handle} {seed : Word}

/-- Retargeting an equal retained handle keeps the exact original checkpoint. -/
def atEntry {entry : Entry} {argument : SourceCorePublicValues.Value} {fuel : Nat}
    (same : entry.handle = handle) (call : StartedCall session handle argument fuel) :
    StartedCall session entry.handle argument fuel :=
  ⟨call.checkpoint,by rw [same]; exact call.accepted⟩

structure IdentityPlan (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    {parameter result : TypeSystem.Ty} (identity : IdentityEntry history.pair.entries handle parameter result)
    (argument : SourceCorePublicValues.Value) (sourceArgument : Dynamic.Value)
    (call : StartedCall session handle argument runOptions.inputValidationFuel) where
  plan : HandleSourcePlan context.first history.pair.retained identity.entry (atEntry identity.handleEq call)
    parameter result sourceArgument sourceArgument
    ⟨history.pair.retained.state.heap.cells ++
      [{type := (identity.shape.principal.parameter.applySubstitution identity.substitution).scheme.body, value := some sourceArgument}]⟩

theorem FullHistory.plan_identity (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    {parameter result : TypeSystem.Ty} (identity : IdentityEntry history.pair.entries handle parameter result)
    {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input history.pair.entries context.selected.packet.header.function.context
      parameter argument sourceArgument)
    (call : StartedCall session handle argument runOptions.inputValidationFuel) :
    Nonempty (IdentityPlan history identity argument sourceArgument call) := by
  obtain ⟨plan⟩ := identity_plan context.first history.pair.retained identity.entry (atEntry identity.handleEq call)
    identity.member identity.entryType (history.pair.origins identity.entry identity.member) input identity.shape
    identity.definitionContext identity.captured identity.substitution identity.evidence identity.sourceEq observed.typing
  exact ⟨⟨plan⟩⟩

theorem IdentityPlan.retained {history : FullHistory context session wordHandle boolHandle captureHandle seed}
    {parameter result : TypeSystem.Ty} {identity : IdentityEntry history.pair.entries handle parameter result}
    {argument : SourceCorePublicValues.Value} {sourceArgument : Dynamic.Value}
    {call : StartedCall session handle argument runOptions.inputValidationFuel}
    (planned : IdentityPlan history identity argument sourceArgument call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  obtain ⟨continued,heapEq,origins⟩ := planned.plan.observed_retained observed.typing history.pair.origins resumed
  have allocated : Dynamic.Heap.Allocates history.pair.retained.state.heap
      (identity.shape.principal.parameter.applySubstitution identity.substitution).scheme.body (some sourceArgument)
      ⟨history.pair.retained.state.heap.cells.length⟩
      ⟨history.pair.retained.state.heap.cells ++
        [{type := (identity.shape.principal.parameter.applySubstitution identity.substitution).scheme.body, value := some sourceArgument}]⟩ := .append
  exact ⟨⟨⟨_,continued,origins,history.pair.wordEntry,history.pair.boolEntry⟩,
    {history.captured with read := heapEq.symm ▸ allocated.preserves_read history.captured.read}⟩⟩

structure CapturedPlan (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    (flag : Bool) (call : StartedCall session captureHandle (.bool flag) runOptions.inputValidationFuel) where
  plan : HandleSourcePlan context.first history.pair.retained history.captured.entry (atEntry history.captured.handleEq call)
    .bool .word (.bool flag) (.word seed)
    ⟨history.pair.retained.state.heap.cells ++
      [{type := (history.captured.shape.principal.parameter.applySubstitution history.captured.substitution).scheme.body, value := some (.bool flag)}]⟩

theorem FullHistory.plan_captured (history : FullHistory context session wordHandle boolHandle captureHandle seed)
    (flag : Bool) (call : StartedCall session captureHandle (.bool flag) runOptions.inputValidationFuel) :
    Nonempty (CapturedPlan history flag call) := by
  have input : RecursiveNamedPublicFunctionHistoryInputs.Input history.pair.entries
      context.selected.packet.header.function.context .bool (.bool flag) (.bool flag) :=
    .data ⟨.bool flag,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool flag⟩ ⟨.bool flag,by simp [SourceCoreIndexedSession.DataInput.publicValue],.bool flag⟩
  obtain ⟨plan⟩ := captured_plan context.first history.pair.retained history.captured.entry
    (atEntry history.captured.handleEq call) history.captured.member history.captured.entryType
    (history.pair.origins history.captured.entry history.captured.member) input history.captured.shape
    history.captured.definitionContext history.captured.captured history.captured.substitution history.captured.evidence
    history.captured.sourceEq history.captured.lookup history.captured.read rfl rfl observed.typing
  exact ⟨⟨plan⟩⟩

theorem CapturedPlan.retained {history : FullHistory context session wordHandle boolHandle captureHandle seed}
    {flag : Bool} {call : StartedCall session captureHandle (.bool flag) runOptions.inputValidationFuel}
    (planned : CapturedPlan history flag call)
    {executionFuel outputFuel : Nat} {returned : SourceCoreExecution.Completion artifact}
    (resumed : call.checkpoint.ResumeAt executionFuel outputFuel (.succeeded returned)) :
    Nonempty (FullHistory context returned.session wordHandle boolHandle captureHandle seed) := by
  obtain ⟨continued,heapEq,origins⟩ := planned.plan.observed_retained observed.typing history.pair.origins resumed
  have allocated : Dynamic.Heap.Allocates history.pair.retained.state.heap
      (history.captured.shape.principal.parameter.applySubstitution history.captured.substitution).scheme.body (some (.bool flag))
      ⟨history.pair.retained.state.heap.cells.length⟩
      ⟨history.pair.retained.state.heap.cells ++
        [{type := (history.captured.shape.principal.parameter.applySubstitution history.captured.substitution).scheme.body, value := some (.bool flag)}]⟩ := .append
  exact ⟨⟨⟨_,continued,origins,history.pair.wordEntry,history.pair.boolEntry⟩,
    {history.captured with read := heapEq.symm ▸ allocated.preserves_read history.captured.read}⟩⟩

end Tests.SourceCoreGeneralizedExport
