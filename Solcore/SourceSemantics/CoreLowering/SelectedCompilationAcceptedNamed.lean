import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionSyntax
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedSourceTyping

/-! One refined accepted body supplies all actual expression actions. Closed
structure and original monomorphic bindings discharge the body boundary;
every remaining expression residual refers to a child of this same receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedNamed
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedBodyAdmission (BodyAt)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)

theorem of_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    (receipt : BodyAt header)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation → Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite directRows instantiation)
    (complete : receipt.tree.complete header.function.resultType = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = [])
    (excluded : ∀ child ∈ receipt.tree.children,
      ¬ Nonempty (AcceptedNamedExpressionFlow.Residual prepared header (DirectSite directRows)
        child.fuel header.function.source child.scope child.expression child.lowered))
    (certified : SelectedCompilationNamedSourceTyping.Certified header) :
    Admission prepared header directRows := by
  have children : ∀ child ∈ receipt.tree.children,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        header.function.source child.expression (DirectSite directRows) := by
    intro child member
    cases AcceptedNamedExpressionFlow.syntax_of_header prepared aligned metadata supported covered child.accepted with
    | inl grammar => exact grammar
    | inr residual => exact False.elim (excluded child member residual)
  obtain ⟨final, facts, typed, _⟩ := certified.statements
  obtain ⟨_facts, certificate⟩ := certified
  have ownership : LocalIdentityOwnership header.function.source := by
    rw [header.frame.source]
    exact certificate.local_identity_ownership
  have bindings := AcceptedNamedBodyBindings.of_monomorphic receipt.tree
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    header.unique ownership typed monomorphic
  exact ⟨metadata, receipt.tree.scan_complete
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
    complete header.unique ownership children bindings typed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedNamed
