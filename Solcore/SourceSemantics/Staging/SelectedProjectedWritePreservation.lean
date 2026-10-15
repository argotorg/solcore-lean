import Solcore.SourceSemantics.Staging.SelectedBareWritePreservation
import Solcore.SourceSemantics.Staging.RecursiveProjectedTarget

/-! Actual typed key values determine the saved projection path. Its getter
heap and the successful RHS heap supply exactly the typing needed by a real
write, without a whole-program execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem Solcore.SourceSemantics.Dynamic

private theorem expression_type_unique {source : TypedSource} {context : Context}
    {id : ExpressionId} {first second : Ty} (unique : NodeOccurrencesUnique source)
    (left : ExpressionHasType source context id first) (right : ExpressionHasType source context id second) :
    first = second := by
  obtain ⟨leftNode, leftFound, leftType⟩ := left.stored_type
  obtain ⟨rightNode, rightFound, rightType⟩ := right.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique leftFound).symm.trans
    (lookupExpression?_complete unique rightFound))
  cases same
  exact leftType.symm.trans rightType

/-- Source typing itself supplies the complete ordered row of key types. -/
theorem projected_keys_typed {source : TypedSource} {context : Context}
    {root leaf : Ty} {projections : List PlaceProjection}
    (typing : SourceProjectionsHaveType source context root projections leaf) :
    ∃ types, ExpressionsHaveTypes source context (ProjectedTarget.keys projections) types := by
  induction projections generalizing root leaf with
  | nil => cases typing; exact ⟨[], .nil _⟩
  | cons projection rest ih =>
      cases projection with
      | member name index =>
          cases typing with
          | member _ path => exact ih path
      | index key =>
          cases typing with
          | index typed path =>
              obtain ⟨types, tail⟩ := ih path
              exact ⟨_ :: types, .cons typed tail⟩

theorem projected_place_keys_typed {source : TypedSource} {context : Context}
    {place : PlaceResolution} {leaf : Ty}
    (typing : SourcePlaceHasType source context place leaf) :
    ∃ types, ExpressionsHaveTypes source context (ProjectedTarget.keys place.projections) types := by
  cases typing with
  | intro _ path _ => exact projected_keys_typed path

/-- The row has the original Source types, independent of native layout types. -/
theorem projected_values_typed {source : TypedSource} {context : Context} {heap : Heap}
    {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List EvaluatedProjection} {root leaf : Ty} {types : List Ty}
    (unique : NodeOccurrencesUnique source)
    (typing : SourceProjectionsHaveType source context root projections leaf)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys projections) types)
    (typedValues : ValuesHaveTypes context heap values types)
    (ordered : ProjectedTarget.Values projections values evaluated) :
    EvaluatedProjectionsHaveType context heap root evaluated leaf := by
  induction ordered generalizing root leaf types with
  | nil => cases typing; exact .nil _
  | member tail ih =>
      cases typing with
      | member selected restTyped =>
          exact .member selected (Dynamic.UniformMemberProjection.preservesType selected)
            (ih restTyped row typedValues)
  | index tail ih =>
      cases typing with
      | index keyTyped restTyped =>
          cases row with
          | cons headType tailType =>
              cases typedValues with
              | cons headValue tailValues =>
                  have same := expression_type_unique unique keyTyped headType
                  exact .index (same.symm ▸ headValue) (ih restTyped tailType tailValues)

/-- The getter reads the root at the actual successful key endpoint. -/
theorem projected_target_typed {source : TypedSource} {context : Context}
    {environment : Dynamic.Environment} {before after : Heap} {place : PlaceResolution}
    {values : List Dynamic.Value} {target : ResolvedPlace} {leaf : Ty} {types : List Ty}
    (unique : NodeOccurrencesUnique source)
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context after) (extension : HeapTypesExtend before after)
    (typed : SourcePlaceHasType source context place leaf)
    (row : ExpressionsHaveTypes source context (ProjectedTarget.keys place.projections) types)
    (typedValues : ValuesHaveTypes context after values types)
    (snapshot : ProjectedTarget.Snapshot environment before after place values target) :
    ∃ root, ResolvedPlaceHasType context after target root leaf := by
  cases typed with
  | @intro _ _ root final writable projections stored =>
      cases snapshot with
      | intro lookup initialRead ordered currentRead initialValue selection =>
          have path := projected_values_typed unique projections row typedValues ordered
          obtain ⟨scheme, staticLookup, _wellFormed, _monomorphic, bodyType⟩ := writable.scheme
          obtain ⟨location, cell, actualLookup, actualRead, cellType, _storage⟩ := locals.lookup staticLookup
          cases lookup.functional actualLookup
          cases initialRead.functional actualRead
          obtain ⟨reached, reachedRead, sameType, _⟩ := extension _ _ initialRead
          cases currentRead.functional reachedRead
          have rootType := sameType.trans (cellType.trans bodyType)
          have initialTyped := initialValue.preserves (heap _ currentRead.member)
          have selectedTyped := selection.preserves path (rootType ▸ initialTyped)
          exact ⟨root, ⟨rootType, stored, path, by simpa [stored] using selectedTyped⟩⟩

/-- Reconstruct the path from the latest root while retaining its earlier snapshot. -/
theorem projected_write_equal {context : Context} {before middle after : Heap}
    {target : ResolvedPlace} {root leaf : Ty} {value updated : Dynamic.Value}
    (targetTyped : ResolvedPlaceHasType context before target root leaf)
    (rhs : ExpressionEvaluationPreserved context before middle value leaf)
    (write : ResolvedPlaceWrites
      (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have currentTarget := targetTyped.mono rhs.heap_extends
  cases write with
  | intro currentRead rootType initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial root := by
        rw [← currentTarget.root_type, ← rootType]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement) leaf := by
        intro current replacement _ applies
        exact applies.equalPreserves rhs.value_typed
      have updatedTyped := update.preserves currentTarget.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootType, currentTarget.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

theorem projected_write_compound {context : Context} {before middle after : Heap}
    {target : ResolvedPlace} {root : Ty} {value updated : Dynamic.Value} {operator : Syntax.ValueAssignOp}
    (kind : WordCompoundAssignmentOperator operator)
    (targetTyped : ResolvedPlaceHasType context before target root .word)
    (rhs : ExpressionEvaluationPreserved context before middle value .word)
    (write : ResolvedPlaceWrites
      (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  have currentTarget := targetTyped.mono rhs.heap_extends
  cases write with
  | intro currentRead rootType initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial root := by
        rw [← currentTarget.root_type, ← rootType]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement) .word := by
        intro current replacement _ applies
        exact applies.wordCompoundPreserves kind currentTarget.selected rhs.value_typed
      have updatedTyped := update.preserves currentTarget.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootType, currentTarget.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
