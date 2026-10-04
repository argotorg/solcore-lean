import Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation

set_option autoImplicit false
namespace Tests.SourceCoreStagingHeapRelation
open Solcore Solcore.SourceSemantics Solcore.SourceSemantics.Dynamic TypeSystem
open Solcore.SourceSemantics.CoreLowering.SourceStagingHeapRelation

/-! The function consumer retains its actual acceptance, full ledger and source
trace. These tests do not claim a compiler has erased the whole call. -/
abbrev actual_function := @integer_function_suffix
abbrev actual_integer_allocation := @HeapRel.erase_allocated
abbrev retained_allocation := @HeapRel.keep_allocated

theorem full_initial_heap {context : Context} {heap : Heap}
    (typed : HeapWellTyped context heap) : HeapRel (identityMap heap.cells.length) heap heap :=
  HeapRel.identity typed

theorem selected_integer_suffix {context : Context} {before : Heap}
    (typed : HeapWellTyped context before) (first second : Int) :
    HeapRel (identityMap before.cells.length ++ [none, none])
      ⟨before.cells ++ [integerCell first, integerCell second]⟩ before := by
  simpa using (HeapRel.identity typed).erase_suffix [first, second]

theorem full_initial_read {before after : Heap} {values : List Int}
    (cells : after.cells = before.cells ++ values.map integerCell)
    {location : Location} {cell : Cell} (read : Heap.Reads before location cell) :
    Heap.Reads after location cell := initial_read cells read

theorem capture_before_suffix {context : Context} {before : Heap} {location : Location}
    (typed : HeapWellTyped context before) (capture : Capture.HeapCaptures before location)
    (offset : Nat) : location.index ≠ before.cells.length + offset := by
  have bound := Capture.heap_bounded typed capture
  omega

theorem integer_result_has_no_capture (value : Int) (location : Location) :
    ¬ Capture.ValueCaptures (.integer value) location := by
  intro captured
  cases captured

section Negative

theorem generalized_cannot_drop (function : GeneralizedClosure) :
    ¬ EligibleDrop ({type := .integer, value := some (.integer 3), generalized := some function} : Cell) :=
  generalized_not_eligible rfl

theorem uninitialized_cannot_drop (type : Ty) :
    ¬ EligibleDrop ({type, value := none} : Cell) := by
  intro eligible
  obtain ⟨value, valueEq⟩ := eligible.fields.2.2
  cases valueEq

theorem captured_drop_impossible {mapping : LocationMap} {function : Closure} {target : Value}
    {id : Resolved.LocalId} {location : Location} (member : (id, location) ∈ function.captured)
    (dropped : mapping[location.index]? = some none) :
    ¬ ValueRel mapping (.closure function) target := by
  intro related
  cases related with
  | closure captured => exact captured.not_dropped member dropped

theorem unused_shadowed_capture_impossible (function : Closure) (id : Resolved.LocalId) :
    ¬ ValueRel [some ⟨0⟩, none]
      (.closure {function with captured := [(id, ⟨0⟩), (id, ⟨1⟩)]}) (.closure function) := by
  apply captured_drop_impossible (id := id) (location := ⟨1⟩)
  · simp
  · rfl

theorem nested_product_capture_impossible (function : Closure) (id : Resolved.LocalId)
    (left right : Value) :
    ¬ ValueRel [none]
      (.product .unit (.closure {function with captured := [(id, ⟨0⟩)]})) (.product left right) := by
  intro related
  cases related with
  | product _ captured =>
      exact captured_drop_impossible (id := id) (location := ⟨0⟩) (by simp) rfl captured

theorem future_capture_cannot_be_typed {context : Context} {heap : Heap} {function : Closure}
    {id : Resolved.LocalId} {location : Location} {type : Ty}
    (member : (id, location) ∈ function.captured) (future : heap.cells.length ≤ location.index) :
    ¬ ValueHasType context heap (.closure function) type := by
  intro typed
  have bound := Capture.value_bounded typed location (.closure member)
  omega

end Negative

section Sharing

/-- The middle source cell is omitted. Both occurrences of the last source
location map to the same residual cell, and the older unused tail remains. -/
theorem ordered_shared_environment (id older : Resolved.LocalId) :
    EnvironmentRel [some ⟨0⟩, none, some ⟨1⟩]
      [(id, ⟨2⟩), (id, ⟨2⟩), (older, ⟨0⟩)]
      [(id, ⟨1⟩), (id, ⟨1⟩), (older, ⟨0⟩)] :=
  .cons rfl (.cons rfl (.cons rfl .nil))

theorem ordered_shared_closure (function : Closure) (id older : Resolved.LocalId) :
    ValueRel [some ⟨0⟩, none, some ⟨1⟩]
      (.closure {function with captured := [(id, ⟨2⟩), (id, ⟨2⟩), (older, ⟨0⟩)]})
      (.closure {function with captured := [(id, ⟨1⟩), (id, ⟨1⟩), (older, ⟨0⟩)]}) :=
  .closure (ordered_shared_environment id older)

theorem original_first_match (id older : Resolved.LocalId) :
    ∃ target, Environment.LooksUp [(id, ⟨1⟩), (id, ⟨1⟩), (older, ⟨0⟩)] id target ∧
      Maps [some ⟨0⟩, none, some ⟨1⟩] ⟨2⟩ target :=
  (ordered_shared_environment id older).lookup .head

theorem distinct_retained_cells {mapping : LocationMap} {length : Nat}
    (ordered : Ordered mapping length) {left right target : Location}
    (first : Maps mapping left target) (second : Maps mapping right target) : left = right :=
  ordered.injective first second

def boolCell (value : Bool) : Cell := {type := .bool, value := some (.bool value)}

theorem retain_drop_retain (erased : Int) :
    HeapRel [some ⟨0⟩, none, some ⟨1⟩]
      ⟨[boolCell false, integerCell erased, boolCell true]⟩
      ⟨[boolCell false, boolCell true]⟩ := by
  have empty : HeapRel [] ⟨[]⟩ ⟨[]⟩ := by
    refine ⟨rfl, .nil, ?_, ?_⟩
    · intro index target cell mapped
      simp at mapped
    · intro index dropped
      simp at dropped
  have first := empty.keep (sourceCell := boolCell false) (residualCell := boolCell false)
    ⟨rfl, .some (.bool false), .none⟩
  have dropped := first.erase_integer erased
  exact dropped.keep ⟨rfl, .some (.bool true), .none⟩

end Sharing
end Tests.SourceCoreStagingHeapRelation
