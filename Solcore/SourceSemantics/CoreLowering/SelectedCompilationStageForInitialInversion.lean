import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentInversion

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds

private theorem restore_twice (outcome : Dynamic.ControlOutcome) (inner outer : Dynamic.Environment) :
    Dynamic.restoreControl outer (Dynamic.restoreControl inner outcome) = Dynamic.restoreControl outer outcome := by
  cases outcome <;> rfl

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context nextContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {items post : List ForItemForm} {test : ExpressionId} {body : List StatementId}
  {size : Nat} {outcome : Dynamic.ControlOutcome}

theorem restored
    (trace : PlainInitial program invocation context environment before items test post body size outcome after) :
    Dynamic.restoreControl environment outcome = outcome := by
  cases trace with
  | initializerFault => rfl
  | loop _ _ => exact restore_twice _ _ _

theorem head {item : ForItemForm}
    (trace : PlainInitial program invocation context environment before (item :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      SourceExecutionSize.ForItemFaults program child context invocation.evidence invocation.source environment before item reason after) ∨
    (∃ child tailSize middleContext nextEnvironment middle nextOutcome,
      child < size ∧ tailSize < size ∧ outcome = Dynamic.restoreControl environment nextOutcome ∧
      SourceExecutionSize.ForItemExecutes program child context invocation.evidence invocation.source environment before item
        middleContext nextEnvironment middle ∧
      PlainInitial program invocation middleContext nextEnvironment middle items test post body tailSize nextOutcome after) := by
  cases trace with
  | initializerFault initial =>
    cases initial with
    | head failed =>
      refine .inl ⟨_, _, ?_, rfl, failed⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | tail executed failed =>
      refine .inr ⟨_, _, _, _, _, _, ?_, ?_, rfl, executed, .initializerFault failed⟩
      all_goals simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
  | loop initial loop =>
    cases initial with
    | cons executed tail =>
      refine .inr ⟨_, _, _, _, _, _, ?_, ?_, (restore_twice _ _ _).symm, executed, .loop tail loop⟩
      all_goals simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega

theorem absent {binder : TypedBinder} (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainInitial program invocation context environment before
      (.letDecl binder none :: items) test post body size outcome after) :
    ∃ tailSize location bound nextOutcome, tailSize < size ∧ outcome = Dynamic.restoreControl environment nextOutcome ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      PlainInitial program invocation nextContext ((binder.id, location) :: environment)
        bound items test post body tailSize nextOutcome after := by
  rcases head trace with ⟨_, _, _, _, failed⟩ | ⟨_, _, _, _, _, _, _, strict, same, executed, tail⟩
  · cases failed; contradiction
  · cases executed with
    | letUninitialized _ extension allocated =>
      cases Dynamic.BinderExtends.functional extended extension
      exact ⟨_, _, _, _, strict, same, allocated, tail⟩

theorem initialized {binder : TypedBinder} {expression : ExpressionId} (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : PlainInitial program invocation context environment before
      (.letDecl binder (some expression) :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle location bound nextOutcome, child < size ∧ tailSize < size ∧
      outcome = Dynamic.restoreControl environment nextOutcome ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      PlainInitial program invocation nextContext ((binder.id, location) :: environment)
        bound items test post body tailSize nextOutcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · cases failed with
    | polymorphicLet poly => exact (poly mono).elim
    | letInitializer _ failed =>
      exact .inl ⟨_, reason, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict, same, .fault failed⟩
  · cases executed with
    | letInitialized evaluated _ extension allocated =>
      cases Dynamic.BinderExtends.functional extended extension
      exact .inr ⟨_, _, _, _, _, _, _,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) childStrict, tailStrict, same,
        .value evaluated, allocated, tail⟩
    | letInitializedGeneralized _ poly => exact (poly mono).elim

theorem discard {expression : ExpressionId}
    (trace : PlainInitial program invocation context environment before
      (.expression expression :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.fault reason) after) ∨
    (∃ child tailSize value middle, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before expression (.value value) middle ∧
      PlainInitial program invocation context environment middle items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · cases failed with
    | expression failed =>
      exact .inl ⟨_, reason, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) strict, same, .fault failed⟩
  · cases executed with
    | expression evaluated =>
      rw [restored tail] at same
      subst outcome
      exact .inr ⟨_, _, _, _, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) childStrict,
        tailStrict, .value evaluated, tail⟩

theorem assign {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {target : Dynamic.ResolvedPlace}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (trace : PlainInitial program invocation context environment before
      (.assignValue assignment operator rhs :: items) test post body size outcome after) :
    (∃ child reason, child < size ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.fault reason) after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧
      outcome = .fault (.invalidAssignmentOperands operator) ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ child tailSize value middle updated written, child < size ∧ tailSize < size ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      PlainInitial program invocation context environment written items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · rcases SelectedCompilationStageForItemsAssignmentInversion.item_fault snapshot failed with
      ⟨child, childStrict, failed⟩ |
      ⟨child, right, currentCell, initial, currentSelected, childStrict, reasonEq, evaluated,
        currentRead, rootType, initialValue, pathRead, invalid⟩
    · exact .inl ⟨child, reason, Nat.lt_trans childStrict strict, same, .fault failed⟩
    · subst reason
      exact .inr (.inl ⟨child, right, currentCell, initial, currentSelected, Nat.lt_trans childStrict strict,
        same, .value evaluated, currentRead, rootType, initialValue, pathRead, invalid⟩)
  · obtain ⟨child, value, middle, updated, strict, rfl, rfl, evaluated, written⟩ :=
      SelectedCompilationStageForItemsAssignmentInversion.item_value snapshot executed
    rw [restored tail] at same
    subst outcome
    exact .inr (.inr ⟨child, _, value, middle, updated, _, Nat.lt_trans strict childStrict, tailStrict,
      .value evaluated, written, tail⟩)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
