import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates

/-! A bare value assignment follows the authenticated compatible callback.
Its actual right-hand action, original binder and emitted place code remain
attached to the same accepted flow action. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces
open CompatibleAssignmentStatements (AssignmentPolicy)

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (output : Ty) (next : Expr)
    (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : AssignmentPolicy policy values invalidProjection invalidOperand missing
  sourceProfile : operator = .equal ∨ assignment.target.type = .word
  bare : assignment.target.projections = []
  accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
    output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment operator (some rhs) output next reasonAt
    (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
    (missing site assignment.target.root) = .ok code
  binder : TypedBinder
  declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder
  place : SourceCoreCompatibleDataPlaces.Prepared
  index : Nat
  child : SourceCoreBasic.LoweredExpr
  rootType : place.route.rootSourceType = binder.scheme.body
  rawType : SourceCoreRawMetadata.runtimeType place.route.rootSourceType =
    SourceCoreRawMetadata.runtimeType assignment.target.type
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, place.route.rootType)
  layout : CompatibleBareAssignment.Layout values place
  generated : policy.lowerExpression fuel source scope rhs reasonAt = .ok child
  childType : child.type = place.route.leafType
  operatorType : operator = .equal ∨ place.route.leafType = .word ∨ place.route.leafType = .integer
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments []) child.expression
    next output (binaryOperator (place.route.leafType = .integer) operator) false
    (invalidOperand site assignment.target.root operator)

/-- Callback equality comes from the compiler policy, before its accepted
action is inverted. No right-hand syntax or execution law is an input. -/
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
    (bare : assignment.target.projections = [])
    (accepted : SourceCoreLoops.assignValue policy fuel source scope site assignment operator rhs
      output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment operator rhs output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment operator (some rhs) output next reasonAt
      (invalidProjection site assignment.target.root) (invalidOperand site assignment.target.root operator)
      (missing site assignment.target.root) = .ok code := by
    cases operator <;> simpa only [SourceCoreLoops.assignValue, matched.equal, matched.value] using accepted
  obtain ⟨binder, place, index, child, declaration, rootType, rawType, slot, layout,
      generated, childType, operatorType, emitted⟩ := CompatibleBareAssignment.of_lower bare lowered
  exact ⟨⟨values, invalidProjection, invalidOperand, missing, matched, sourceProfile, bare, accepted, lowered,
    binder, declaration, place, index, child, rootType, rawType, slot, layout, generated,
    childType, operatorType, emitted⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedBareAssignmentReceipt
