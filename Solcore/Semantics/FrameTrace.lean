import Solcore.Semantics.FrameEffectJournal

/-! Finite chronological traces for opt-in frame-effect observations. -/

set_option autoImplicit false

namespace Solcore.Semantics

universe u

/-- A finite chronological sequence built through explicit extension operations. -/
structure FrameTrace (Event : Type u) : Type u where private mk ::
  private events : List Event

namespace FrameTrace

/-- The trace containing no events. -/
def empty {Event : Type u} : FrameTrace Event :=
  ⟨[]⟩

/-- Observe events from earliest to latest. -/
def toList {Event : Type u} (trace : FrameTrace Event) : List Event :=
  trace.events

/-- Place every event in the earlier trace before every event in the later trace. -/
def append {Event : Type u}
    (earlier later : FrameTrace Event) : FrameTrace Event :=
  ⟨earlier.events ++ later.events⟩

/-- Record one event after every event already in the trace. -/
def record {Event : Type u}
    (trace : FrameTrace Event) (event : Event) : FrameTrace Event :=
  ⟨trace.events ++ [event]⟩

end FrameTrace

end Solcore.Semantics
