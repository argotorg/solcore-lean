import Solcore.Semantics.FrameTrace

/-! Observation and extension algebra for finite chronological frame traces. -/

set_option autoImplicit false

namespace Solcore.Semantics.FrameTrace

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

end Solcore.Semantics.FrameTrace
