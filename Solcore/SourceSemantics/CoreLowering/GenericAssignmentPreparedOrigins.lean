import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLayoutCertificates

/-! The selected assignment head retains its actual compiler preparation.
Bare roots keep their genuine empty projection receipt. Projected routes keep
same-site description and preparation of the exact selected head, beside its
actual path layout. These are static receipts only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

/-- All site, fuel and diagnostic arguments are those used by the successful
assignment lowering that produced this same head. -/
inductive Head.PreparedAt
    (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (site : SourceCoreElaboration.ErrorSite) (fuel : Nat) (invalidProjection : Word)
    (missing : TypeSystem.Ty → Word) : Prop where
  | bare (empty : assignment.target.projections = []) :
      head.PreparedAt site fuel invalidProjection missing
  | projected {sourceTypes : List TypeSystem.Ty} (route : Route)
      (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := definitions) values source certificate
        scope site assignment.target head.prepared head.codes sourceTypes head.leaf administrative)
      (ordinary : (∀ key value, head.prepared.route.rootSourceType ≠ .mapping key value) →
        head.prepared.route.rootMapping = none)
      (shape : head.shape = .projected layout ordinary)
      (described : describe values values.checked.signatures source site assignment = .ok route)
      (preparedBy : prepare values fuel route invalidProjection missing = .ok head.prepared) :
      head.PreparedAt site fuel invalidProjection missing

end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
