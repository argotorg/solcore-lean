import Solcore.SourceSemantics.Staging.SelectedControlPreservationContracts
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

theorem bare_target_typed
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before : Heap} {place : PlaceResolution} {target : ResolvedPlace} {type : Ty}
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (typed : SourcePlaceHasType source context place type)
    (snapshot : BareTarget environment before place target) :
    ∃ rootType, ResolvedPlaceHasType context before target rootType type := by
  cases typed with
  | @intro _ _ rootType finalType writable projections stored =>
      cases snapshot with
      | @intro location cell initial bare lookup read value =>
          rw [bare] at projections
          cases projections
          obtain ⟨scheme, staticLookup, _wellFormed, _monomorphic, bodyEq⟩ := writable.scheme
          obtain ⟨staticLocation, staticCell, actualLookup, actualRead, typeEq, _storage⟩ := locals.lookup staticLookup
          have locationEq := lookup.functional actualLookup
          subst staticLocation
          have cellEq := read.functional actualRead
          subst staticCell
          have rootEq : cell.type = type := typeEq.trans bodyEq
          refine ⟨type, ⟨rootEq, stored, .nil _,  ?_⟩⟩
          exact rootEq ▸ value.preserves (heap cell read.member)

theorem bare_write
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before middle after : Heap} {place : PlaceResolution} {target : ResolvedPlace}
    {value updated : Value} {type : Ty}
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (targetTyped : SourcePlaceHasType source context place type)
    (snapshot : BareTarget environment before place target)
    (rhs : ExpressionEvaluationPreserved context before middle value type)
    (write : ResolvedPlaceWrites (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  obtain ⟨rootType, targetBefore⟩ := bare_target_typed locals heap targetTyped snapshot
  have targetMiddle := targetBefore.mono rhs.heap_extends
  cases write with
  | intro currentRead rootEq initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial rootType := by
        rw [← targetMiddle.root_type, ← rootEq]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies .equal target.selected value replacement) type := by
        intro current replacement _currentTyped applies
        exact applies.equalPreserves rhs.value_typed
      have updatedTyped := update.preserves targetMiddle.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootEq, targetMiddle.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

theorem bare_write_compound
    {source : TypedSource} {context : Context} {environment : Dynamic.Environment}
    {before middle after : Heap} {place : PlaceResolution} {target : ResolvedPlace}
    {value updated : Value} {operator : Syntax.ValueAssignOp}
    (kind : WordCompoundAssignmentOperator operator)
    (locals : EnvironmentAgrees before context.locals environment)
    (heap : HeapWellTyped context before)
    (targetTyped : SourcePlaceHasType source context place .word)
    (snapshot : BareTarget environment before place target)
    (rhs : ExpressionEvaluationPreserved context before middle value .word)
    (write : ResolvedPlaceWrites (fun _ replacement => AssignmentValueApplies operator target.selected value replacement)
      middle target updated after) :
    HeapWellTyped context after ∧ HeapTypesExtend before after := by
  obtain ⟨rootType, targetBefore⟩ := bare_target_typed locals heap targetTyped snapshot
  have targetMiddle := targetBefore.mono rhs.heap_extends
  cases write with
  | intro currentRead rootEq initialValue update heapWrite =>
      rename_i currentCell initial
      have initialTyped := initialValue.preserves (rhs.heap_typed _ currentRead.member)
      have initialRoot : OptionalValueHasType context middle initial rootType := by
        rw [← targetMiddle.root_type, ← rootEq]
        exact initialTyped
      have modification : LeafModificationPreservesType context middle
          (fun _ replacement => AssignmentValueApplies operator target.selected value replacement) .word := by
        intro current replacement _currentTyped applies
        exact applies.wordCompoundPreserves kind targetMiddle.selected rhs.value_typed
      have updatedTyped := update.preserves targetMiddle.projections initialRoot modification
      have updatedCell : ValueHasType context middle updated currentCell.type := by
        rw [rootEq, targetMiddle.root_type]
        exact updatedTyped
      exact ⟨rhs.heap_typed.write currentRead (.some updatedCell) heapWrite,
        rhs.heap_extends.trans (HeapTypesExtend.of_write heapWrite)⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
