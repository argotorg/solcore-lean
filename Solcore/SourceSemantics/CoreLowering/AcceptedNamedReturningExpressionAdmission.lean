import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionBoundaryExclusion

/-! A genuine returning Header body supplies its own expression actions.
Original reached forms discharge every residual and yield the existing admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedExpressionFlow
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

/-- The accepted body and its children are recovered before expression syntax.
The original return head closes the actual body and excludes local bindings. -/
theorem of_returning {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    {reached : ExpressionId → Prop}
    (forms : ReachedForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments header.function.source reached)
    (present : reached expression)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases of_receipt prepared aligned receipt metadata supported covered wellFormed with
  | inl admission => exact admission
  | inr failures =>
    obtain ⟨failure⟩ := failures
    cases failure with
    | «structure» actual openBranch =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.1] at openBranch
      cases openBranch
    | generalized actual binding member quantified =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.2.1] at member
      cases member
    | expression actual child member residual =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      have childReached : reached child.expression := (details.2.2 child member).symm ▸ present
      exact False.elim (residual.impossible metadata forms initializers arguments childReached)

/-- The accepted body and its children are recovered before expression syntax.
The original return head closes the actual body and excludes local bindings. -/
theorem of_returning_calls {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : MetadataFor compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (roots : header.function.body = id :: rest)
    (found : header.function.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    {reached : ExpressionId → Prop}
    (forms : ReachedCallForms header.function.source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed prepared.named) id))
    (arguments : ReachedCallArguments header.function.source reached)
    (rawMetadata : ReachedIndirectMetadata compiled.indexed prepared.named header.function.source reached)
    (present : reached expression)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  cases of_receipt prepared aligned receipt metadata supported covered wellFormed with
  | inl admission => exact admission
  | inr failures =>
    obtain ⟨failure⟩ := failures
    cases failure with
    | «structure» actual openBranch =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.1] at openBranch
      cases openBranch
    | generalized actual binding member quantified =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      rw [details.2.1] at member
      cases member
    | expression actual child member residual =>
      have details := actual.tree.at_return_list
        (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) roots found form
      have childReached : reached child.expression := (details.2.2 child member).symm ▸ present
      exact False.elim (residual.impossible_calls metadata forms initializers arguments rawMetadata childReached)

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
