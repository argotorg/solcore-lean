import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionResidual
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionTraceSyntax

/-! Genuine Header acceptance supplies the entire recursive action trace. Its
original expression grammar is derived only after those actions are recovered. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

/-- The result uses the genuine selected policy and actual ordered child calls.
Metadata and supported target rows stay explicit static premises. -/
theorem syntax_of_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {directSites : DeclarationInstantiation → Prop}
    {fuel : Nat} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named source directSites)
    (supported : ∀ instantiation, directSites instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) → directSites instantiation)
    (accepted : header.policy.lowerExpression fuel source scope id header.reasonAt = .ok lowered) :
    GeneralSyntax source id directSites ∨ Nonempty (Residual prepared header directSites fuel source scope id lowered) := by
  obtain ⟨predecessor, sameFuel, root, _head⟩ := of_header prepared aligned accepted
  obtain ⟨tree⟩ := Trace.of_accepted (root := root) metadata supported covered root.selected.accepted
  cases Trace.syntax_or_boundary tree covered with
  | inl grammar => exact .inl grammar
  | inr boundaries =>
    obtain ⟨boundary⟩ := boundaries
    exact .inr ⟨⟨accepted, predecessor, sameFuel, root, tree, boundary⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
