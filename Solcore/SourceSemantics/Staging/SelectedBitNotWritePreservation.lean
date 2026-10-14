import Solcore.SourceSemantics.Staging.SelectedBareWritePreservation

/-! A bare unary write preserves the actual raw Word cell type. No expression
preservation hypothesis is needed for the absent right-hand side. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

theorem bare_write_bitNot
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before after : Heap} {assignment : AssignmentResolution} {target : ResolvedPlace}
    {updated : Value}
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (typed : SourceBitNotAssignmentValid source context assignment)
    (snapshot : BareTarget environment before assignment.target target)
    (write : ResolvedPlaceWrites (fun _ replacement => BitNotSnapshot target.selected replacement)
      before target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  cases typed with
  | intro targetTyped _ =>
    obtain ⟨rootType, targetTyped⟩ := bare_target_typed locals heap targetTyped snapshot
    cases write with
    | intro currentRead rootEq initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (heap _ currentRead.member)
      have initialRoot : OptionalValueHasType context before initial rootType := by
        rw [← targetTyped.root_type, ← rootEq]
        exact initialTyped
      have modification : LeafModificationPreservesType context before
          (fun _ replacement => BitNotSnapshot target.selected replacement) .word := by
        intro current replacement _ applies
        exact applies.preserves targetTyped.selected
      have updatedTyped := update.preserves targetTyped.projections initialRoot modification
      have updatedCell : ValueHasType context before updated currentCell.type := by
        rw [rootEq, targetTyped.root_type]
        exact updatedTyped
      exact ⟨heap.write currentRead (.some updatedCell) heapWrite,
        HeapTypesExtend.of_write heapWrite⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
