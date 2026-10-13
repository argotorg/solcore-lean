import Solcore.SourceSemantics.CoreLowering.AcceptedMethodBodyAdmission
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog

/-! A genuine method instantiation supplies original Source typing for the
actual cached body. Its accepted statement and expression actions construct
the existing method certificate, preserving its full synthetic specialization. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedMethods
open Core Frontend SourceInference
open AcceptedMethodBodyReceipts
open AcceptedNamedBodyFlow AcceptedNamedExpressionFlow
open CallablePreparedMethodSelection (Cached)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots (DirectSource)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedScopedMethodAdmission (SourceCertificate)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

theorem child_syntax
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (forms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    {scope : SourceCoreLocalCell.Scope} {fuel : Nat} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : (policy cached).lowerExpression fuel (source cached) scope id
      (reasonAt cached) = .ok lowered) (present : reached id) :
    GeneralSyntax (source cached) id (DirectSite table.rows) := by
  obtain ⟨catalog⟩ := SelectedCompilationCatalog.of_compiled compiled bodies
  obtain ⟨predecessor, _same, ⟨root⟩⟩ := policy_receipt cached accepted
  obtain ⟨trace⟩ := Trace.of_accepted (root := root) metadata
    (fun _ site => site.supported (table.aligned catalog)) covered root.selected.accepted
  cases trace.syntax_or_boundary covered with
  | inl grammar => exact grammar
  | inr residual =>
    obtain ⟨boundary⟩ := residual
    exact False.elim (boundary.impossible metadata forms initializers arguments present)


theorem source_typing
    (certified : ∃ types context facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method)
        types context facts) :
    ∃ context final facts,
      StatementsHaveType (source cached) {returnType := cached.named.specialized.function.inferredBodyType}
        context cached.compilation.statements final facts ∧
      NodeOccurrencesUnique (source cached) ∧ LocalIdentityOwnership (source cached) := by
  obtain ⟨types, context, facts, typed⟩ := certified
  have sameSource : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).source =
      source cached := by
    simp only [source, CallableIndexedNamedGeneration.source, cached.same,
      CallableCoercionMethodInstantiation.bodyInstance]
  have sameResult : (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method).resultType =
      cached.named.specialized.function.inferredBodyType := by
    rw [cached.same]
    rfl
  have body := typed.typing.body_typed
  rw [sameSource, sameResult] at body
  obtain ⟨final, body, _roots, _complete⟩ := body
  change StatementsHaveType (source cached)
    {returnType := cached.named.specialized.function.inferredBodyType}
    context (statements (source cached)) final facts at body
  rw [AcceptedMethodBodyAdmission.roots cached] at body
  exact ⟨context, final, facts, body,
    sameSource ▸ typed.graph_closed.wellFormed.nodeOccurrencesUnique,
    sameSource ▸ typed.local_identity_ownership⟩

theorem of_certificate
    (certified : ∃ types context facts,
      Dynamic.BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method)
        types context facts)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨context, final, facts, typed, unique, ownership⟩ := source_typing cached certified
  have binders := AcceptedNamedBodyBindings.of_monomorphic receipt.tree (read cached)
    unique ownership typed monomorphic
  have grammar : ∀ child ∈ receipt.tree.children,
      GeneralSyntax (source cached) child.expression (DirectSite table.rows) := by
    intro child member
    exact child_syntax cached table bodies metadata covered reachedForms arguments initializers
      child.accepted (children child member)
  have body := receipt.tree.scan (read cached) closed unique grammar binders typed
  rw [← AcceptedMethodBodyAdmission.roots cached] at body
  exact ⟨⟨forms, ⟨metadata, body⟩⟩⟩

theorem of_selection
    (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (selected : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (parameters : selected.implementation.parameters.Nodup)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (SourceSemantics.Context.ofSignatures compiled.sourceProgram.signatures)
      method.specialized.parameterSubstitution)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    (table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled)
    (receipt : BodyAt cached)
    (forms : DirectSource (source cached))
    (metadata : MetadataFor compiled.indexed cached.named (source cached) (DirectSite table.rows))
    (covered : ∀ id node, (source cached).lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
        DirectSite table.rows instantiation)
    {reached : ExpressionId → Prop}
    (reachedForms : ReachedForms (source cached) reached)
    (arguments : ReachedArguments (source cached) reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (CallableIndexedNamedGeneration.context compiled.indexed cached.named) id))
    (children : ∀ child ∈ receipt.tree.children, reached child.expression)
    (closed : receipt.tree.closed = true)
    (monomorphic : ∀ binding ∈ receipt.tree.bindings, binding.binder.scheme.quantified = []) :
    Nonempty (SourceCertificate compiled cached.named table.rows) := by
  obtain ⟨definition, member, identity, instantiated⟩ :=
    AcceptedMethodBodyAdmission.instantiates_of_selection checked selected parameters range
  obtain ⟨retained, retainedMember, retainedId, retainedBody⟩ := selected.retained checked
  have retainedValid := bodies.methods retained
    ⟨cached.index, cached.named, method, cached.selected, cached.same, selected,
      retainedMember, retainedId, retainedBody⟩
  have sameDefinition : definition = MethodDefinition.ofChecked retained :=
    StructuralSubstitution.eq_of_mem_of_mapped_nodup bodies.method_ids member
      (List.mem_map.mpr ⟨retained, retainedMember, rfl⟩)
      (identity.trans (retainedId.trans selected.methodId).symm)
  have valid : MethodDefinition.Valid compiled.sourceProgram.signatures definition :=
    sameDefinition ▸ retainedValid
  obtain ⟨types, context, facts, certificate⟩ := instantiated.certificate_of_valid bodies.signatures valid
  exact of_certificate cached ⟨types, context, facts, certificate.toBodyInstanceTypingCertificate⟩
    bodies table receipt forms metadata covered reachedForms arguments initializers children closed monomorphic

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedMethods
