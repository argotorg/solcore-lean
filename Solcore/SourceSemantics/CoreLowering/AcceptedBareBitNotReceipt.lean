import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementCertificates

/-! The actual absent-RHS callback retains the original bare Word target and
complete emitted update. It contributes no expression child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
open Core Frontend SourceInference
open SourceCoreCompatibleDataPlaces

structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (output : Ty) (next : Expr)
    (reasonAt : ExpressionId → Word) (code : Expr) where
  values : SourceCoreCompatibleValues.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missing : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  matched : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missing
  sourceProfile : assignment.target.type = .word
  bare : assignment.target.projections = []
  callback : ExpressionLowerer → Nat → TypedSource → SourceCoreLocalCell.Scope →
    SourceCoreElaboration.ErrorSite → AssignmentResolution → Ty → Expr →
    (ExpressionId → Word) → Except SourceCoreBasic.Error Expr
  selected : policy.assignBitNotWithExpression = some callback
  accepted : callback policy.lowerExpression fuel source scope site assignment
    output next reasonAt = .ok code
  lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
    assignment .equal none output next reasonAt
    (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
    (missing site assignment.target.root) = .ok code
  binder : TypedBinder
  declaration : SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder
  place : SourceCoreCompatibleDataPlaces.Prepared
  index : Nat
  rootType : place.route.rootSourceType = binder.scheme.body
  rawType : SourceCoreRawMetadata.runtimeType place.route.rootSourceType =
    SourceCoreRawMetadata.runtimeType assignment.target.type
  slot : SourceCoreLocalCell.lookup? scope assignment.target.root = some (index, place.route.rootType)
  layout : CompatibleBareBitNotCertificates.Layout place
  emitted : code = execute place (.var index) (SourceCoreCalls.packArguments [])
    (LanguageResult.success .unit) next output
    (binaryOperator (place.route.leafType = .integer) .equal) true
    (invalidUnary site assignment.target.root)

/-- The callback and accepted action determine the original layout and token.
Raw Word eligibility is retained separately from the native numeric view. -/
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
    (bare : assignment.target.projections = [])
    (selected : policy.assignBitNotWithExpression = some callback)
    (accepted : callback policy.lowerExpression fuel source scope site assignment
      output next reasonAt = .ok code) :
    Nonempty (Receipt policy fuel source scope site assignment output next reasonAt code) := by
  have lowered : lower values values.checked.signatures policy.lowerExpression fuel source scope site
      assignment .equal none output next reasonAt
      (invalidProjection site assignment.target.root) (invalidUnary site assignment.target.root)
      (missing site assignment.target.root) = .ok code := by
    have same := Option.some.inj (selected.symm.trans matched)
    simpa only [same] using accepted
  have numeric : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer :=
    .inl (by rw [sourceProfile]; rfl)
  obtain ⟨binder, place, index, declaration, rootType, rawType, slot, layout, emitted⟩ :=
    CompatibleBareBitNotCertificates.of_lower bare numeric lowered
  exact ⟨⟨values, invalidProjection, invalidUnary, missing, matched, sourceProfile, bare,
    callback, selected, accepted, lowered, binder, declaration, place, index, rootType, rawType,
    slot, layout, emitted⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
