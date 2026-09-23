import Solcore.ContractRuntime.FrameEffectJournal

/-! Finite chronological traces for opt-in frame-effect observations. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

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

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceProperties`
-/

/-! Observation and extension algebra for finite chronological frame traces. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

@[simp] theorem toList_empty {Event : Type u} :
    (empty : FrameTrace Event).toList = [] := by
  rfl

@[simp] theorem toList_append {Event : Type u}
    (earlier later : FrameTrace Event) :
    (append earlier later).toList = earlier.toList ++ later.toList := by
  rfl

@[simp] theorem toList_record {Event : Type u}
    (trace : FrameTrace Event) (event : Event) :
    (record trace event).toList = trace.toList ++ [event] := by
  rfl

theorem toList_injective {Event : Type u} :
    Function.Injective (toList : FrameTrace Event → List Event) := by
  intro left right same
  cases left
  cases right
  simp only [toList] at same
  congr

@[simp] theorem append_empty_left {Event : Type u}
    (trace : FrameTrace Event) :
    append empty trace = trace := by
  cases trace
  rfl

@[simp] theorem append_empty_right {Event : Type u}
    (trace : FrameTrace Event) :
    append trace empty = trace := by
  apply toList_injective
  change trace.toList ++ [] = trace.toList
  have appendNil : ∀ events : List Event, events ++ [] = events := by
    intro events
    induction events with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  exact appendNil trace.toList

theorem append_assoc {Event : Type u}
    (first second third : FrameTrace Event) :
    append (append first second) third = append first (append second third) := by
  apply toList_injective
  change (first.toList ++ second.toList) ++ third.toList =
    first.toList ++ (second.toList ++ third.toList)
  have appendAssoc : ∀ left middle right : List Event,
      (left ++ middle) ++ right = left ++ (middle ++ right) := by
    intro left middle right
    induction left with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  exact appendAssoc first.toList second.toList third.toList

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTracePrefix`
-/

/-! Non-strict prefix factorization for finite chronological frame traces. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

/-- An earlier trace whose ordered extension equals the later trace. -/
def IsPrefixOf {Event : Type u}
    (earlier later : FrameTrace Event) : Prop :=
  ∃ fragment, later = append earlier fragment

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTracePrefixProperties`
-/

/-! Canonical witnesses and transitivity for ordered trace prefixes. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.FrameTrace

universe u

theorem empty_isPrefixOf {Event : Type u}
    (trace : FrameTrace Event) :
    IsPrefixOf empty trace :=
  ⟨trace, (append_empty_left trace).symm⟩

theorem isPrefixOf_refl {Event : Type u}
    (trace : FrameTrace Event) :
    IsPrefixOf trace trace :=
  ⟨empty, (append_empty_right trace).symm⟩

theorem isPrefixOf_append {Event : Type u}
    (earlier fragment : FrameTrace Event) :
    IsPrefixOf earlier (append earlier fragment) :=
  ⟨fragment, rfl⟩

theorem isPrefixOf_trans
    {Event : Type u} {first second third : FrameTrace Event}
    (firstSecond : IsPrefixOf first second)
    (secondThird : IsPrefixOf second third) :
    IsPrefixOf first third := by
  rcases firstSecond with ⟨middleFragment, rfl⟩
  rcases secondThird with ⟨lastFragment, rfl⟩
  exact ⟨append middleFragment lastFragment,
    append_assoc first middleFragment lastFragment⟩

end Solcore.ContractRuntime.FrameTrace

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceExtension`
-/

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

/-!
## Consolidated module: `Solcore.ContractRuntime.FrameTraceExtensionProperties`
-/

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
