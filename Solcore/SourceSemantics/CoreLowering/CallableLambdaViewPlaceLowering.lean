import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder

/-! Place lowering keeps the actual view expression callback while preserving
original binders and complete reached key nodes. No evaluation is transported. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPlaceLowering
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open CallableLambdaViewEdits CallableLambdaBodyReachability

theorem key_reference {projections : List PlaceProjection} {id : ExpressionId}
    (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    .expression id ∈ projections.flatMap PlaceProjection.references := by
  induction projections with
  | nil => cases member
  | cons projection rest ih =>
      cases projection with
      | member name index => exact ih member
      | index key =>
          rcases List.mem_cons.mp member with same | member
          · subst id
            simp [PlaceProjection.references]
          · exact List.mem_append_right _ (ih member)

private theorem routes {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view)
    {checked : Checked} {signatures : ProgramSignatures} {site : SourceCoreElaboration.ErrorSite}
    {root : Resolved.LocalId} {projections : List PlaceProjection}
    (keys : ∀ id ∈ DataPlaceKeyOrder.sourceKeys projections, source.lookupExpression? id = view.lookupExpression? id)
    (type : TypeSystem.Ty) :
    routeSteps checked signatures source site root type projections =
      routeSteps checked signatures view site root type projections := by
  induction projections generalizing type with
  | nil => rfl
  | cons projection rest ih =>
      cases projection with
      | member name index =>
          simp only [routeSteps, ih keys]
      | index key =>
          have first := keys key (List.mem_cons_self)
          have rest := fun id member => keys id (List.mem_cons_of_mem _ member)
          simp only [routeSteps, metadata.owner, first, ih rest]

theorem lower {source view : TypedSource} (metadata : LambdaMetadataViews.MetadataView source view)
    {values : SourceCoreCompatibleValues.Context} {signatures : ProgramSignatures} {expression : ExpressionLowerer}
    {fuel : Nat} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : Option ExpressionId}
    {output : Ty} {next : Expr} {reasonAt : ExpressionId → Word}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (keys : ∀ id ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections,
      source.lookupExpression? id = view.lookupExpression? id) :
    SourceCoreCompatibleDataPlaces.lower values signatures (fun fuel _ scope id reasonAt => expression fuel view scope id reasonAt)
        fuel source scope site assignment operator rhs output next reasonAt invalidProjection invalidOperand missing =
      SourceCoreCompatibleDataPlaces.lower values signatures expression fuel view scope site assignment operator rhs output next reasonAt
        invalidProjection invalidOperand missing := by
  have rootEq : SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root =
      SourceCoreCompatibleDataPlaces.rootBinder view assignment.target.root :=
    CallableLambdaBodyReachability.rootBinder metadata _
  have route : describe values signatures source site assignment = describe values signatures view site assignment := by
    simp only [describe, rootEq, routes metadata keys]
  simp only [SourceCoreCompatibleDataPlaces.lower, route]

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewPlaceLowering
