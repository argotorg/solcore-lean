import Solcore.SourceSemantics.Staging.SelectedProjectedWritePreservation

/-! The actual typed key endpoint supplies admission for a projected unary write. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedBitNotAdmission
open Frontend SourceInference Staging.Recursive

theorem heap_after_bitNot
    {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {environment : Dynamic.Environment}
    {before getter after : Dynamic.Heap} {types : List TypeSystem.Ty} {values : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (typed : SourceBitNotAssignmentValid source context assignment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys assignment.target.projections) types)
    (keyValues : Dynamic.ValuesHaveTypes context getter values types)
    (getterHeap : Dynamic.HeapWellTyped context getter)
    (getterMetadata : Dynamic.HeapTypesExtend before getter)
    (snapshot : ProjectedTarget.Snapshot environment before getter assignment.target values target)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
      getter target updated after) :
    Dynamic.HeapWellTyped context after := by
  cases typed with
  | intro targetTyped _ =>
      obtain ⟨root, savedTyped⟩ := SelectedPreservation.projected_target_typed unique locals
        getterHeap getterMetadata targetTyped row keyValues snapshot
      exact (SelectedPreservation.projected_write_bitNot savedTyped getterHeap write).1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedBitNotAdmission
