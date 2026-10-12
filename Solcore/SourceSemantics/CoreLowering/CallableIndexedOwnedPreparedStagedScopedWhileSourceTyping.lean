import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites

/-! Original Source typing supplies the condition, scoped body and suffix at
the same outer context. No loop execution or result is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements) :
    Statements source context rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, context, _, .nil _ _⟩
  | cons head tail =>
      obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      have same : actual = node := Option.some.inj
        ((lookupStatement?_complete unique contains).symm.trans found)
      subst actual
      rw [form] at formTyped
      cases formTyped
      exact ⟨control, final, _, tail⟩

theorem children {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements) :
    ExpressionHasType source context condition .bool ∧ Statements source context statements :=
  ProtectedStateImperativeTypedSourceSites.while_loop unique
    (ProtectedStateImperativeTypedSourceSites.head typed) found form

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
