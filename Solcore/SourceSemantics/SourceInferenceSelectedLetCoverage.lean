import Solcore.SourceSemantics.SourceInferenceSelectedStatementReferences

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

theorem localSchemeTemplateOwner_binder_of_let
    {source : TypedSource} {id : StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {owner : LocalSchemeTemplateOwner}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder (some initializer))
    (ownerContains : ContainsLocalSchemeTemplate source owner)
    (initializerEq : owner.initializer = .expression initializer) : owner.binder = binder := by
  have edge : DirectChild source (.statement id) (.expression initializer) :=
    directChild_statement_reference contains (by simp [form, StatementForm.references])
  obtain ⟨ownerNode, ownerContains, bindingMem, ownerEdge⟩ :=
    InitializedLetBinding.owningStatement (owner.binding_mem ownerContains)
  have ownerEdge' : DirectChild source (.statement ownerNode.id) (.expression initializer) := by
    simpa only [initializerEq] using ownerEdge
  have parentEq : ownerNode.id = id := by
    have nodesEq := closed.childHasUniqueParent ownerEdge' edge
    cases nodesEq
    rfl
  have nodeEq : ownerNode = node := by
    have ownerLookup := lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique ownerContains
    have parentLookup := lookupStatement?_complete closed.wellFormed.nodeOccurrencesUnique contains
    rw [parentEq, parentLookup] at ownerLookup
    exact Option.some.inj ownerLookup.symm
  subst ownerNode
  have bindingEq : ({binder := owner.binder, initializer := owner.initializer} : InitializedLetBinding) =
      {binder, initializer := .expression initializer} := by
    simpa only [form, statementInitializedLetBindings, List.mem_singleton] using bindingMem
  exact congrArg InitializedLetBinding.binder bindingEq

theorem templateScopeCovered_letInitializer
    {source : TypedSource} {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId}
    (closed : OccurrenceGraphClosed source)
    (contains : ContainsStatement source id node)
    (form : node.form = .letDecl binder (some initializer))
    (covered : TemplateScopeCovered source context (.statement id)) :
    TemplateScopeCovered source (localSchemeInitializerContext context binder) (.expression initializer) := by
  apply TemplateScopeCovered.localSchemeInitializer_of_newRoots covered closed.childHasUniqueParent
    (directChild_statement_reference contains (by simp [form, StatementForm.references]))
  intro owner ownerContains initializerEq
  have binderEq := localSchemeTemplateOwner_binder_of_let closed contains form ownerContains initializerEq
  simpa only [binderEq] using owner.requirement_mem ownerContains

end Solcore.SourceSemantics.SourceInferenceSoundness
