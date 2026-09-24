import Solcore.SourceSemantics.Dynamic.Typing

/-! Focused proof consumers for generalized-closure cell typing. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsGeneralizedClosureTyping

open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def ordinaryHeap : Heap := {
  cells := [{ type := .bool, value := some (.bool false) }]
}

/-- Adding generalized metadata to `CellWellTyped` leaves ordinary cells on
the existing value-typing path. -/
example (context : Context) : HeapWellTyped context ordinaryHeap := by
  intro cell member
  simp only [ordinaryHeap, List.mem_singleton] at member
  subst cell
  exact ⟨.some (.bool false), .none .bool⟩

/-- A deeply typed principal closure inhabits a descriptor cell exactly at its
scheme body. -/
example {context : Context} {heap : Heap} {function : GeneralizedClosure}
    (typed : GeneralizedClosureWellTyped context heap function) :
    CellWellTyped context heap {
      type := function.binder.scheme.body
      value := none
      generalized := some function
    } :=
  ⟨.none _, .some typed⟩

/-- Descriptor inversion recovers both the principal cell type and the
closure's deep typing witness. -/
example {context : Context} {heap : Heap} {function : GeneralizedClosure}
    (typed : GeneralizedClosureWellTyped context heap function) :
    function.binder.scheme.body = function.binder.scheme.body ∧
      GeneralizedClosureWellTyped context heap function := by
  exact OptionalGeneralizedClosureWellTyped.some_inv (.some typed)

/-- Fresh generalized allocation extends any well-typed heap when its
principal closure is already valid in the old heap world. -/
example {context : Context} {before after : Heap} {function : GeneralizedClosure}
    {location : Location}
    (before_typed : HeapWellTyped context before)
    (function_typed : GeneralizedClosureWellTyped context before function)
    (allocation : Heap.AllocatesGeneralized before function location after) :
    HeapWellTyped context after :=
  before_typed.allocateGeneralized function_typed allocation

/-- Metadata-preserving heap growth supplies the existing type-extension
interface without discarding its stronger descriptor guarantee. -/
example {before after : Heap}
    (extension : HeapMetadataExtend before after) :
    HeapTypesExtend before after :=
  extension.toTypes

/-- Generalized closure typing transports across both supported context
changes and type-preserving heap growth. -/
example {source target : Context} {before after : Heap}
    {function : GeneralizedClosure}
    (supports : TypeContextSupports source target)
    (extension : HeapTypesExtend before after)
    (typed : GeneralizedClosureWellTyped source before function) :
    GeneralizedClosureWellTyped target after function :=
  (typed.transportContext supports).mono extension

/-- Ordinary allocation preserves the complete descriptor of every older
cell, not only its declared type. -/
example {before after : Heap} {type : Ty} {value : Option Value}
    {fresh old : Location} {cell : Cell}
    (allocation : Heap.Allocates before type value fresh after)
    (read : Heap.Reads before old cell) :
    ∃ updatedCell,
      Heap.Reads after old updatedCell ∧
      updatedCell.type = cell.type ∧
      updatedCell.generalized = cell.generalized :=
  HeapTypesExtend.of_allocation allocation old cell read

/-- A value write leaves the selected cell's generalized descriptor intact. -/
example {before after : Heap} {written old : Location}
    {value : Option Value} {cell : Cell}
    (write : Heap.Writes before written value after)
    (read : Heap.Reads before old cell) :
    ∃ updatedCell,
      Heap.Reads after old updatedCell ∧
      updatedCell.type = cell.type ∧
      updatedCell.generalized = cell.generalized :=
  HeapTypesExtend.of_write write old cell read

/-- Descriptor preservation composes transitively across multiple heap
steps. -/
example {first middle last : Heap} {location : Location} {cell : Cell}
    (left : HeapTypesExtend first middle)
    (right : HeapTypesExtend middle last)
    (read : Heap.Reads first location cell) :
    ∃ updatedCell,
      Heap.Reads last location updatedCell ∧
      updatedCell.type = cell.type ∧
      updatedCell.generalized = cell.generalized :=
  left.trans right location cell read

end Solcore.Test.SourceSemanticsGeneralizedClosureTyping
