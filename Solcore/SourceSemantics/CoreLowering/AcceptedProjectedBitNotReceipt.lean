import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceCompilerCertificates

/-! A projected unary update retains its actual absent-RHS callback and
ordered key actions. The administrative Unit is not a Source expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProjectedBitNotReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces
open DataPatternValues DataPlaceCertificates CompatibleMixedRoute

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution)
    (output : Ty) (next : Expr) (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing
  sourceProfile : assignment.target.type = .word
  projected : assignment.target.projections ≠ []
  callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
    SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
    (ExpressionId → Word) → Except SourceCoreBasic.Error Expr
  callbackSelected : policy.assignBitNotWithExpression = some callback
  accepted : callback policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment .equal none output next reasonAt
    (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
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
  leafType : place.route.leafType = .word ∨ place.route.leafType = .integer
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments keys) (LanguageResult.success .unit)
    next output (binaryOperator (place.route.leafType = .integer) .equal) true
    (invalidUnary site assignment.target.root)

/-- The accepted callback supplies the actual keys, route and unary token. -/
theorem of_accepted {policy : SourceCoreLoops.Policy} {values : SourceCoreCompatibleValues.Context}
    {invalidProjection invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {output : Ty} {next code : Expr} {reasonAt : ExpressionId → Word}
    {callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
      SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
      (ExpressionId → Word) → Except SourceCoreBasic.Error Expr}
    (matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing)
    (sourceProfile : assignment.target.type = .word)
    (projected : assignment.target.projections ≠ [])
    (callbackSelected : policy.assignBitNotWithExpression = some callback)
    (accepted : callback policy.lowerExpression fuel source scope site assignment output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment .equal none output next reasonAt
      (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
      (missing site assignment.target.root) = .ok code := by
    have same := Option.some.inj (callbackSelected.symm.trans matched)
    simpa only [same] using accepted
  cases CompatiblePlaceCompilerCertificates.generated_of_lower lowered with
  | intro route place index keys value described slot prepared keysGenerated operatorValid rhsGenerated =>
    cases rhsGenerated with
    | absent =>
      obtain ⟨binder, selected, description⟩ := CompatiblePlaceDescription.of_describe described
      obtain ⟨routeType, _, path⟩ := description.prepared prepared
      have leafType : place.route.leafType = .word ∨ place.route.leafType = .integer := by
        simpa only [Option.isNone_none, Bool.true_eq_false, and_false, false_or, routeType] using operatorValid
      refine ⟨⟨values, invalidProjection, invalidUnary, missing, matched, sourceProfile,
        projected, _, callbackSelected, accepted, lowered, route, binder, selected, description,
        place, prepared, routeType, path, index, slot, keys, keysGenerated,
        CompatiblePlaceCompilerCertificates.PreparedPath.key_ids path, leafType, ?_⟩⟩
      simp only [routeType, Option.isNone_none]

end Solcore.SourceSemantics.CoreLowering.AcceptedProjectedBitNotReceipt
