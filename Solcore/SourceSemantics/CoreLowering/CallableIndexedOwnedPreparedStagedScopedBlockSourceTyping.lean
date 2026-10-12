import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites

/-! Original Source typing supplies the scoped block body and suffix at the
same entry context. No execution or result is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements) :
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

theorem inner {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements) :
    Statements source context statements :=
  ProtectedStateImperativeTypedSourceSites.block_typed unique
    (ProtectedStateImperativeTypedSourceSites.head typed) found form

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
