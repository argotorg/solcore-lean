import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReachedReads
import Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingCertificates

/-! Fixed-control checker typing supplies the static Source facts consumed at
each accepted compiler statement. The actual compiler read selects the node;
typing never chooses a different statement or expression. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
open Core Frontend SourceInference

variable {source : TypedSource}

/-- The original statement typing splits at the node read by the compiler. -/
theorem head_form (unique : NodeOccurrencesUnique source)
    {control : ControlContext} {context final : SourceSemantics.Context} {id : StatementId}
    {rest : List StatementId} {facts : BodyFacts} {node : StatementNode}
    (typed : StatementsHaveType source control context (id :: rest) final facts)
    (found : source.lookupStatement? id = some node) :
    ∃ middle restFacts, Dynamic.StatementHasType.FormTyping source control context node.form middle ∧
      StatementsHaveType source control middle rest final restFacts := by
  cases typed with
  | singleton head =>
    obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    have same : original = node :=
      Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst same
    exact ⟨_, _, formTyped, .nil _ _⟩
  | cons head tail =>
    obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    have same : original = node :=
      Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst same
    exact ⟨_, _, formTyped, tail⟩

/-- Expression typing identifies the unique original node and its stored type. -/
theorem expression_node (unique : NodeOccurrencesUnique source)
    {context : SourceSemantics.Context} {id : ExpressionId} {type : TypeSystem.Ty}
    (typed : ExpressionHasType source context id type) :
    ∃ node, source.lookupExpression? id = some node ∧ node.type = type ∧
      ExpressionHasType source context id node.type := by
  have original := typed
  cases typed with
  | intro contains _ _ _ _ _ => exact ⟨_, lookupExpression?_complete unique contains, rfl, original⟩

/-- A monomorphic binder uses the catalog projection in every actual body
policy, named or contextual. -/
theorem binder_projected {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : ActualBodyInvocation.BodyRelation} (index : ActualBodyInvocation.Index compiled bodyRelation)
    {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = [])
    (accepted : index.policy.lowerBinder source scope binder = .ok payload) :
    compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload := by
  cases index with
  | named receipt selected =>
    simp only [ActualBodyInvocation.Index.policy, AcceptedNamedBodyFlow.namedPolicy,
      SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte] at accepted
    exact CompatibleStatementBindings.binder_projected accepted
  | contextual material view =>
    simp only [ActualBodyInvocation.Index.policy, GeneralizedLocalAcceptedBodyCompiler.policy,
      GeneralizedLocalLambdaCompilation.binder, SourceCoreGeneralFunctions.contextualBinder, mono,
      List.isEmpty_nil, ↓reduceIte, GeneralizedLocalLambdaCompilation.representation] at accepted
    rw [material.indexed.represented] at accepted
    exact CompatibleStatementBindings.binder_projected accepted

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
