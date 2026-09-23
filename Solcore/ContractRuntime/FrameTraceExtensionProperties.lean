import Solcore.ContractRuntime.FrameTraceExtension
import Solcore.ContractRuntime.FrameTraceProperties

/-! Observation laws for indexed incremental frame-trace extension. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace.ExtensionFrom

universe u

@[simp] theorem toTrace_start
    {Event : Type u} (earlier : FrameTrace Event) :
    (start earlier).toTrace = earlier := by
  change FrameTrace.append earlier FrameTrace.empty = earlier
  exact FrameTrace.append_empty_right earlier

@[simp] theorem toTrace_record
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) (event : Event) :
    (extension.record event).toTrace =
      FrameTrace.record extension.toTrace event := by
  refine ExtensionFrom.rec (motive := fun extension =>
    (extension.record event).toTrace =
      FrameTrace.record extension.toTrace event) ?_ extension
  intro fragment
  change FrameTrace.append earlier
      (FrameTrace.append fragment (FrameTrace.record FrameTrace.empty event)) =
    FrameTrace.append (FrameTrace.append earlier fragment)
      (FrameTrace.record FrameTrace.empty event)
  exact (FrameTrace.append_assoc earlier fragment
    (FrameTrace.record FrameTrace.empty event)).symm

end Solcore.ContractRuntime.FrameTrace.ExtensionFrom
