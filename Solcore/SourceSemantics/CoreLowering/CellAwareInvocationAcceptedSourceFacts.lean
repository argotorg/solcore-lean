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

/-- The actual statement read also locates the node in the compiler's view. -/
theorem compiler_read {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : ActualBodyInvocation.BodyRelation} (index : ActualBodyInvocation.Index compiled bodyRelation)
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type)) :
    index.compilerSource.lookupStatement? id = some node := by
  rw [index.statement_reader] at accepted
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ index.compilerSource.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : index.compilerSource.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨_, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

/-- Header items extend the lexical context without changing its signatures. -/
theorem items_signatures {control : ControlContext} {signatures : ProgramSignatures} :
    ∀ {items : List ForItemForm} {context final : SourceSemantics.Context},
      ForItemsHaveType source control context items final →
      context.signatures = signatures → final.signatures = signatures
  | [], _, _, typed, same => by
    cases typed
    exact same
  | _ :: _, _, _, typed, same => by
    cases typed with
    | cons head tail =>
      apply items_signatures tail
      cases head with
      | letUninitialized _ _ extension => cases extension; exact same
      | letInitialized _ _ _ extension => cases extension; exact same
      | letInitializedGeneralized _ _ _ _ extension => cases extension; exact same
      | expression => exact same
      | assignValue => exact same
      | assignBitNot => exact same

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSourceFacts
