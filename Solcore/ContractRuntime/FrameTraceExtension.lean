import Solcore.ContractRuntime.FrameTracePrefix

/-! Event-only incremental extension from one indexed earlier frame trace. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

/-- An incremental trace fragment whose earlier trace is fixed by its type. -/
structure ExtensionFrom
    {Event : Type u} (earlier : FrameTrace Event) : Type u where private mk ::
  private fragment : FrameTrace Event

namespace ExtensionFrom

/-- Begin an extension without adding an event. -/
def start {Event : Type u}
    (earlier : FrameTrace Event) : ExtensionFrom earlier :=
  ⟨FrameTrace.empty⟩

/-- Observe the fixed earlier trace followed by every recorded event. -/
def toTrace {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) : FrameTrace Event :=
  FrameTrace.append earlier extension.fragment

/-- Record one event at the chronological tail of the extension. -/
def record {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) (event : Event) :
    ExtensionFrom earlier :=
  ⟨FrameTrace.record extension.fragment event⟩

/-- The fixed earlier trace is a prefix of every observed extension. -/
theorem earlier_isPrefixOf_toTrace
    {Event : Type u} {earlier : FrameTrace Event}
    (extension : ExtensionFrom earlier) :
    FrameTrace.IsPrefixOf earlier extension.toTrace :=
  ⟨extension.fragment, rfl⟩

end ExtensionFrom

end Solcore.ContractRuntime.FrameTrace
