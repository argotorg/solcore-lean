import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentAdmission
import Solcore.SourceSemantics.Staging.SelectedProjectedWritePreservation

/-! Final projected writes use the actual successful key and RHS endpoints.
Original Source key types are retained independently of native layout types. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
open Frontend SourceInference Staging.Recursive

/-- The original assignment, ordered key values and actual RHS admission
supply deep heap typing for the real write at the latest root. -/
theorem heap_after_assignment
    {source : TypedSource} {context : SourceSemantics.Context}
    {operator : Syntax.ValueAssignOp}
    {assignment : AssignmentResolution} {rhs : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before getter middle after : Dynamic.Heap}
    {types : List TypeSystem.Ty} {values : List Dynamic.Value}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment operator rhs)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys assignment.target.projections) types)
    (keyValues : Dynamic.ValuesHaveTypes context getter values types)
    (getterHeap : Dynamic.HeapWellTyped context getter)
    (getterMetadata : Dynamic.HeapTypesExtend before getter)
    (snapshot : ProjectedTarget.Snapshot environment before getter assignment.target values target)
    (heapTyped : Dynamic.HeapWellTyped context middle)
    (rightTyped : Dynamic.ValueHasType context middle right node.type)
    (rhsMetadata : Dynamic.HeapTypesExtend getter middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    Dynamic.HeapWellTyped context after := by
  cases typed with
  | equal targetTyped rhsTyped _ =>
      obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
      have sameNode : actual = node := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst actual
      obtain ⟨root, savedTyped⟩ := SelectedPreservation.projected_target_typed unique locals
        getterHeap getterMetadata targetTyped row keyValues snapshot
      have rightSource := storedType ▸ rightTyped
      exact (SelectedPreservation.projected_write_equal savedTyped
        ⟨rightSource, heapTyped, rhsMetadata⟩ write).1
  | wordCompound kind targetTyped rhsTyped _ =>
      obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
      have sameNode : actual = node := Option.some.inj
        ((lookupExpression?_complete unique contains).symm.trans found)
      subst actual
      obtain ⟨root, savedTyped⟩ := SelectedPreservation.projected_target_typed unique locals
        getterHeap getterMetadata targetTyped row keyValues snapshot
      have rightSource := storedType ▸ rightTyped
      exact (SelectedPreservation.projected_write_compound kind savedTyped
        ⟨rightSource, heapTyped, rhsMetadata⟩ write).1

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
