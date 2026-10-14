import Solcore.SourceSemantics.SourceInferenceSelectedAssignmentChildren

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem sourcePlace_transportExpressions {before after : TypedSource}
    {context : SourceSemantics.Context} {place : PlaceResolution} {type : Ty}
    (typed : SourcePlaceHasType before context place type)
    (children : ∀ id, .expression id ∈ place.references → ∀ type,
      ExpressionHasType before context id type → ExpressionHasType after context id type) :
    SourcePlaceHasType after context place type := by
  have projections {input output : Ty} {projections : List PlaceProjection}
      (typed : SourceProjectionsHaveType before context input projections output)
      (children : ∀ id, .expression id ∈ projections.flatMap PlaceProjection.references → ∀ type,
        ExpressionHasType before context id type → ExpressionHasType after context id type) :
      SourceProjectionsHaveType after context input projections output := by
    induction projections generalizing input output with
    | nil => cases typed; exact .nil _
    | cons projection rest induction =>
      cases typed with
      | index key tail =>
        exact .index (children _ (by simp [PlaceProjection.references]) _ key)
          (induction tail (fun id member => children id (by simp [member])))
      | member selected tail =>
        exact .member selected (induction tail (fun id member => children id (by simp [member])))
  cases typed with
  | intro root rest same => exact .intro root (projections rest children) same

theorem sourceAssignment_transportExpressions {before after : TypedSource}
    {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {value : ExpressionId}
    (typed : SourceAssignmentHasType before context assignment operator value)
    (children : ∀ id, .expression id ∈ assignment.references ++ [.expression value] → ∀ type,
      ExpressionHasType before context id type → ExpressionHasType after context id type) :
    SourceAssignmentHasType after context assignment operator value := by
  have place {type : Ty} (typed : SourcePlaceHasType before context assignment.target type) :
      SourcePlaceHasType after context assignment.target type :=
    sourcePlace_transportExpressions typed (fun id member => children id (by simp [AssignmentResolution.references, member]))
  cases typed with
  | equal target value requirements => exact .equal (place target) (children _ (by simp) _ value) requirements
  | wordCompound operator target value requirements =>
    exact .wordCompound operator (place target) (children _ (by simp) _ value) requirements

theorem ActualStateInvariant.ofForItemPreservingBinders
    {fuel : Nat} {context : Frontend.SourceInference.Context}
    {item : Syntax.ForItem} {initial final : State} {inferred : ForItemForm} {source : TypedSource}
    (invariant : ActualStateInvariant initial source)
    (success : Detail.inferForItemFuel fuel context item initial = .ok (inferred, final))
    (bindersEq : final.localBinders = initial.localBinders)
    (nextLe : initial.inference.next ≤ final.inference.next) : ActualStateInvariant final source := by
  obtain ⟨pending, ledger⟩ := invariant.ledger
  exact ⟨⟨pending ++ inferred.localSchemeTemplateIds, (actualLedgerFamily fuel).statements.forItem success ledger⟩,
    invariant.origins.congr_localBinders bindersEq,
    activeQuantifiersBelowNext_transport invariant.quantifiersBelow bindersEq nextLe, invariant.sourceMonomorphic⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
