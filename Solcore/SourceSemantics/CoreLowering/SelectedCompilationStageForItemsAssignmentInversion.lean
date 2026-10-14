import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsSourceInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentInversion
open Frontend SourceInference
open SelectedCompilationStageForLiftBounds
open Staging.Recursive (BareTarget)

private theorem target_functional {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {place : PlaceResolution} {left right : Dynamic.ResolvedPlace}
    (first : BareTarget environment heap place left) (second : BareTarget environment heap place right) : left = right := by
  cases first with
  | intro _ leftLookup leftRead leftValue =>
    cases second with
    | intro _ rightLookup rightRead rightValue =>
      cases leftLookup.functional rightLookup
      cases leftRead.functional rightRead
      cases leftValue.functional rightValue
      rfl

private theorem resolve_same {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target actual : Dynamic.ResolvedPlace} {size : Nat}
    (snapshot : BareTarget environment before place target)
    (resolved : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place actual after) :
    after = before ∧ actual = target := by
  have bare : place.projections = [] := by cases snapshot; assumption
  obtain ⟨same, other⟩ := BareTarget.of_resolves bare resolved.sound
  exact ⟨same.symm, target_functional other snapshot⟩

private theorem target_fault_excluded {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target : Dynamic.ResolvedPlace} {reason : Dynamic.SemanticFault}
    (snapshot : BareTarget environment before place target)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after) : False := by
  cases snapshot with
  | intro bare present cell initial =>
    cases fault with
    | unbound missing => exact missing.excludes_lookup present
    | dangling lookup missing =>
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionExpression _ _ failed => rw [bare] at failed; cases failed
    | danglingAfterProjections lookup _ evaluated missing =>
      rw [bare] at evaluated
      cases evaluated
      cases lookup.functional present
      exact missing.excludes_read cell
    | projectionRead _ _ evaluated _ _ failed =>
      rw [bare] at evaluated
      cases evaluated
      cases failed
    | uninitialized _ _ evaluated _ _ _ nonempty =>
      rw [bare] at evaluated
      cases evaluated
      exact nonempty rfl

variable {program : Program} {invocation : Staging.Recursive.Scope}
  {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  {target : Dynamic.ResolvedPlace} {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem item_value {nextEnvironment : Dynamic.Environment}
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.ForItemExecutes program size context invocation.evidence invocation.source environment
      before (.assignValue assignment operator rhs) finalContext nextEnvironment after) :
    ∃ child value middle updated, child < size ∧ finalContext = context ∧ nextEnvironment = environment ∧
      SourceExecutionSize.ExpressionEvaluates program child context invocation.evidence invocation.source environment
        before rhs value middle ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated after := by
  cases trace with
  | assignValue assigned =>
    cases assigned with
    | intro resolved evaluated written =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      refine ⟨_, _, _, _, ?_, rfl, rfl, evaluated, written⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega

theorem item_fault
    (snapshot : BareTarget environment before assignment.target target)
    (trace : SourceExecutionSize.ForItemFaults program size context invocation.evidence invocation.source environment
      before (.assignValue assignment operator rhs) reason after) :
    (∃ child, child < size ∧
      SourceExecutionSize.ExpressionFaults program child context invocation.evidence invocation.source environment
        before rhs reason after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧
      reason = .invalidAssignmentOperands operator ∧
      SourceExecutionSize.ExpressionEvaluates program child context invocation.evidence invocation.source environment
        before rhs right after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) := by
  cases trace with
  | assignValue failed =>
    cases failed with
    | target failed => exact (target_fault_excluded snapshot failed.sound).elim
    | rhs resolved failed =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      refine .inl ⟨_, ?_, failed⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      refine .inr ⟨_, _, _, _, _, ?_, rfl, evaluated, currentRead, rootType, initialValue, pathRead, invalid⟩
      simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega
    | structuralUpdate resolved _ _ _ _ failed =>
      obtain ⟨rfl, rfl⟩ := resolve_same snapshot resolved
      cases snapshot
      cases failed

theorem child_and_tail {rest : List ForItemForm}
    (snapshot : BareTarget environment before assignment.target target)
    (trace : PlainItems program size invocation context environment before
      (.assignValue assignment operator rhs :: rest) finalContext outcome after) :
    (∃ child reason, child < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      RecursiveNamedCallBounds.ExpressionOutcome program child context invocation.evidence invocation.source
        environment before rhs (.fault reason) after) ∨
    (∃ child right currentCell initial currentSelected, child < size ∧ finalContext = context ∧
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
      PlainItems program tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | done trace =>
    cases trace with
    | cons head tail =>
      obtain ⟨child, value, middle, updated, strict, rfl, rfl, evaluated, written⟩ := item_value snapshot head
      exact .inr (.inr ⟨child, _, value, middle, updated, _,
        Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
        SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, written, .done tail⟩)
  | fault trace =>
    cases trace with
    | head failed =>
      rcases item_fault snapshot failed with
        ⟨child, strict, failed⟩ |
        ⟨child, right, currentCell, initial, currentSelected, strict, reasonEq, evaluated,
          currentRead, rootType, initialValue, pathRead, invalid⟩
      · exact .inl ⟨child, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)), rfl, rfl, .fault failed⟩
      · cases reasonEq
        exact .inr (.inl ⟨child, right, currentCell, initial, currentSelected,
          Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)), rfl, rfl,
          .value evaluated, currentRead, rootType, initialValue, pathRead, invalid⟩)
    | tail head failed =>
      obtain ⟨child, value, middle, updated, strict, rfl, rfl, evaluated, written⟩ := item_value snapshot head
      exact .inr (.inr ⟨child, _, value, middle, updated, _,
        Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
        SourceExecutionSize.child_lt_stepSize (by simp), .value evaluated, written, .fault failed⟩)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentInversion
