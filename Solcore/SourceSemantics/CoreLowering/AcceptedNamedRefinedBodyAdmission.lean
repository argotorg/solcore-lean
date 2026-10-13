import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyRefinement
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionSyntax

/-! One refined accepted body supplies all actual expression actions. Closed
structure and original monomorphic bindings discharge the body boundary;
every remaining expression residual refers to a child of this same receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
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
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = [])
    (excluded : ∀ child ∈ receipt.tree.children,
      ¬ Nonempty (AcceptedNamedExpressionFlow.Residual prepared header (DirectSite directRows)
        child.fuel header.function.source child.scope child.expression child.lowered))
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  have children : ∀ child ∈ receipt.tree.children,
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        header.function.source child.expression (DirectSite directRows) := by
    intro child member
    cases AcceptedNamedExpressionFlow.syntax_of_header prepared aligned metadata supported covered child.accepted with
    | inl grammar => exact grammar
    | inr residual => exact False.elim (excluded child member residual)
  cases AcceptedNamedBodyBindings.of_header prepared aligned wellFormed receipt.tree with
  | inl bindings =>
    obtain ⟨final, facts, typed, _⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
    exact ⟨metadata, receipt.tree.scan
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
      closed header.unique children bindings typed⟩
  | inr generalized =>
    obtain ⟨binding, member, different⟩ := generalized
    exact False.elim (different (monomorphic binding member))

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedRefinedBodyAdmission
