import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionSyntax

/-! Each child of one actual accepted body is admitted from its own compiler
action. Original Header typing supplies lexical binding facts. Unsupported
branches retain that same whole body and, when relevant, the actual child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
open Core Frontend SourceInference
open AcceptedNamedBodyFlow
open AcceptedNamedBodyAdmission (BodyAt)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedScopedAdmission (Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

/-- The original body and ordered child membership remain part of the residual.
No failure from a different body or detached source occurrence is substituted. -/
inductive Unsupported (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | structure (receipt : BodyAt header) (openBranch : receipt.tree.closed = false)
  | generalized (receipt : BodyAt header) (binding : Binding header.policy header.function.source)
      (member : binding ∈ receipt.tree.bindings) (quantified : binding.binder.scheme.quantified ≠ [])
  | expression (receipt : BodyAt header)
      (child : Child header.policy header.function.source header.reasonAt)
      (member : child ∈ receipt.tree.children)
      (residual : AcceptedNamedExpressionFlow.Residual prepared header (DirectSite directRows)
        child.fuel header.function.source child.scope child.expression child.lowered)

include aligned

/-- This producer consumes a single actual body receipt. Every child is handled
by accepted-expression inversion; no child syntax callback or body scan runs. -/
theorem of_receipt {directRows : List SourceSpecialization.SpecializedFunction}
    (receipt : BodyAt header)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows ∨ Nonempty (Unsupported prepared header directRows) := by
  classical
  cases closed : receipt.tree.closed with
  | false => exact .inr ⟨.structure receipt closed⟩
  | true =>
    rcases AcceptedNamedBodyBindings.of_header prepared aligned wellFormed receipt.tree with binders | generalized
    · by_cases children : ∀ child ∈ receipt.tree.children,
        GeneralSyntax header.function.source child.expression (DirectSite directRows)
      · obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
        exact .inl ⟨metadata, receipt.tree.scan
          (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned)
          closed header.unique children binders typed⟩
      · obtain ⟨child, absent⟩ := Classical.not_forall.mp children
        have member : child ∈ receipt.tree.children := Classical.byContradiction fun missing =>
          absent (fun present => False.elim (missing present))
        have missing : ¬ GeneralSyntax header.function.source child.expression (DirectSite directRows) :=
          fun grammar => absent (fun _ => grammar)
        cases AcceptedNamedExpressionFlow.syntax_of_header prepared aligned metadata
            supported covered child.accepted with
        | inl grammar => exact False.elim (missing grammar)
        | inr residual => exact .inr ⟨.expression receipt child member (Classical.choice residual)⟩
    · obtain ⟨binding, member, quantified⟩ := generalized
      exact .inr ⟨.generalized receipt binding member quantified⟩

/-- The body receipt itself is recovered from the genuine aligned Header action. -/
theorem of_actual {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      Supported compiled.indexed.base.plan instantiation)
    (covered : ∀ id node, header.function.source.lookupExpression? id = some node →
      ∀ callee args instantiation, node.form = .call callee args (.declaration instantiation) →
        DirectSite directRows instantiation)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    Admission prepared header directRows ∨ Nonempty (Unsupported prepared header directRows) := by
  obtain ⟨receipt⟩ := body_of_accepted aligned.accepted
  exact of_receipt prepared aligned receipt metadata supported covered wellFormed

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
