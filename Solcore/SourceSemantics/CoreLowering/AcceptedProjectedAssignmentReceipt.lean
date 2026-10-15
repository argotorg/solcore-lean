import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates

/-! A projected value assignment retains the actual place preparation and
ordered key actions. Its declared root and selected leaf remain distinct;
the receipt does not assume execution of a key, getter or right-hand action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces
open CompatibleAssignmentStatements (AssignmentPolicy)
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : AssignmentPolicy policy values invalidProjection invalidOperand missing
  sourceProfile : operator = .equal ∨ assignment.target.type = .word
  projected : assignment.target.projections ≠ []
  accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
    output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment operator (some rhs) output next reasonAt
    (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
    (missing site assignment.target.root) = .ok code
  route : Route
  binder : TypedBinder
  selected : TypeSystem.Ty
  description : CompatiblePlaceDescription.Description values source site assignment route binder selected
  place : Prepared
  prepared : prepare values fuel route (invalidProjection site assignment.target.root)
    (missing site assignment.target.root) = .ok place
  routeType : place.route = route
  path : PreparedPath values.checked source site binder.scheme.body assignment.target.projections
    0 place.steps place.keys selected
  index : Nat
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, route.rootType)
  keys : List SourceCoreBasic.LoweredExpr
  keysGenerated : ListRel (KeyGenerated policy.lowerExpression fuel source scope reasonAt) place.keys keys
  keyIds : place.keys.map Prod.fst = DataPlaceKeyOrder.sourceKeys assignment.target.projections
  child : SourceCoreBasic.LoweredExpr
  generated : policy.lowerExpression fuel source scope rhs reasonAt = .ok child
  childType : child.type = place.route.leafType
  operatorType : operator = .equal ∨ place.route.leafType = .word ∨ place.route.leafType = .integer
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments keys) child.expression
    next output (binaryOperator (place.route.leafType = .integer) operator) false
    (invalidOperand site assignment.target.root operator)

/-- The same successful compiler callback supplies its original route,
ordered keys and RHS. Repeated key occurrences remain repeated actions. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    (matched : AssignmentPolicy policy values invalidProjection invalidOperand missing)
    (sourceProfile : operator = .equal ∨ assignment.target.type = .word)
    (projected : assignment.target.projections ≠ [])
    (accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
      output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment operator rhs output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment operator (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
      (missing site assignment.target.root) = .ok code := by
    cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted
  cases CompatiblePlaceCompilerCertificates.generated_of_lower lowered with
  | intro route place index keys value described slot prepared keysGenerated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | @present id child generated childType =>
      obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeType, _, path⟩ := description.prepared prepared
      have operatorType : operator = .equal ∨ place.route.leafType = .word ∨ place.route.leafType = .integer := by
        rw [routeType]
        rcases operatorValid with equal | word | integer
        · exact .inl equal.1
        · exact .inr (.inl word)
        · exact .inr (.inr integer)
      refine ⟨⟨values, invalidProjection, invalidOperand, missing, matched, sourceProfile,
        projected, accepted, lowered, route, binder, selected, description, place, prepared,
        routeType, path, index, slot, keys, keysGenerated,
        CompatiblePlaceCompilerCertificates.PreparedPath.key_ids path,
        child, generated, ?_, operatorType, ?_⟩⟩
      · simpa only [routeType] using childType.symm
      · simp only [routeType, Option.isNone_some]

end Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentReceipt
