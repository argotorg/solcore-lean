import Solcore.SourceSemantics.SourceInferenceActualRootedContracts

/-! Actual statement references retain enclosing initializer scopes. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open SourceInferenceStatementsSoundness

theorem ActualContext.Covers.statement_reference
    {finalized : Frontend.SourceInference.Result} {frames : List InitializedLetBinding}
    {id : StatementId} {node : StatementNode} {child : NodeId}
    (covered : ActualContext.Covers finalized frames (.statement id))
    (contains : ContainsStatement finalized.typedSource id node)
    (reference : child ∈ node.form.references) :
    ActualContext.Covers finalized frames child := by
  apply covered.directChild
  refine ⟨.statement node, ⟨contains.1, ?_⟩, reference⟩
  simpa [Node.id] using congrArg NodeId.statement contains.2

theorem SubtreePreserved.containsStatement
    {substitution : Substitution} {before after : TypedSource}
    {id : StatementId} {node : StatementNode}
    (preserved : SubtreePreserved substitution before after (.statement id))
    (contains : ContainsStatement before id node) :
    ContainsStatement after id (node.applySubstitution substitution) := by
  refine ⟨preserved.nodes (.statement node) contains.1 (.inl ?_), ?_⟩
  · simpa [Node.id] using congrArg NodeId.statement contains.2
  · simpa using contains.2

theorem RawSubtreePreserved.finalized
    {wholeContext : Frontend.SourceInference.Context} {wholeReturn : Ty}
    {evidenceState : State} {roots : List NodeId}
    {finalized : Frontend.SourceInference.Result} {before : TypedSource} {root : NodeId}
    (preserved : RawSubtreePreserved before (evidenceState.toTypedSource roots) root)
    (resources : FinalInferenceResources wholeContext wholeReturn evidenceState roots finalized) :
    SubtreePreserved finalized.substitution before finalized.typedSource root := by
  rw [resources.source_eq]
  exact preserved.substituted finalized.substitution

theorem directChild_statement_reference
    {source : TypedSource} {id : StatementId} {node : StatementNode} {child : NodeId}
    (contains : ContainsStatement source id node) (reference : child ∈ node.form.references) :
    DirectChild source (.statement id) child := by
  refine ⟨.statement node, ⟨contains.1, ?_⟩, reference⟩
  simpa [Node.id] using congrArg NodeId.statement contains.2

theorem SubtreePreserved.directChild
    {substitution : Substitution} {before after : TypedSource} {root child : NodeId}
    (preserved : SubtreePreserved substitution before after root)
    (edge : DirectChild before root child) : DirectChild after root child := by
  obtain ⟨node, contains, reference⟩ := edge
  refine ⟨node.applySubstitution substitution, ⟨preserved.nodes node contains.1 (.inl contains.2), ?_⟩, ?_⟩
  · simpa using contains.2
  · simpa [nodeChildIds] using reference

theorem ActualContext.Covers.preserved_statement_reference
    {substitution : Substitution} {before : TypedSource}
    {finalized : Frontend.SourceInference.Result} {frames : List InitializedLetBinding}
    {id : StatementId} {node : StatementNode} {child : NodeId}
    (covered : ActualContext.Covers finalized frames (.statement id))
    (contains : ContainsStatement before id node)
    (preserved : SubtreePreserved substitution before finalized.typedSource (.statement id))
    (reference : child ∈ node.form.references) : ActualContext.Covers finalized frames child :=
  covered.directChild (preserved.directChild (directChild_statement_reference contains reference))

theorem rooted_statement_child_covered
    {substitution : Substitution} {before after : TypedSource}
    {parentContext childContext : SourceSemantics.Context}
    {id child : StatementId} {node : StatementNode}
    (contains : ContainsStatement before id node)
    (reference : (.statement child : NodeId) ∈ node.form.references)
    (preserved : SubtreePreserved substitution before after (.statement id))
    (covered : TemplateScopeCovered after parentContext (.statement id))
    (closed : OccurrenceGraphClosed after)
    (assumptions : parentContext.assumptions ⊆ childContext.assumptions) :
    TemplateScopeCovered after childContext (.statement child) :=
  TemplateScopeCovered.statementChild covered closed
    (preserved.directChild (directChild_statement_reference contains reference)) assumptions

end Solcore.SourceSemantics.SourceInferenceSoundness
