import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites

/-! The accepted Source head fixes the exact lexical context of its suffix.
These inversions require no execution trace or separate body typing premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

private theorem suffix_of_form
    {source : TypedSource} {context next : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (contextAt : ∀ control final,
      Dynamic.StatementHasType.FormTyping source control context node.form final → final = next) :
    Statements source next rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, next, _, .nil _ _⟩
  | cons head tail =>
    obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
    have same : actual = node := Option.some.inj
      ((lookupStatement?_complete unique contains).symm.trans found)
    subst actual
    exact contextAt _ _ formTyped ▸ ⟨control, final, _, tail⟩

/-- Initialized and uninitialized lets use the actual retained binder
extension, including when Source typing admits a generalized initializer. -/
theorem let_decl
    {source : TypedSource} {context next : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : Option ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder initializer)
    (extended : BinderExtends source.owner context binder next) :
    Statements source next rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original with
  | letUninitialized _ actual | letInitialized _ _ actual
  | letInitializedGeneralized _ _ _ _ actual =>
    exact Dynamic.BinderExtends.functional actual extended

/-- An expression statement leaves the suffix's lexical context unchanged. -/
theorem discard
    {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression : ExpressionId} {semicolon : Bool}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon) :
    Statements source context rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original <;> rfl

/-- Plain and compound assignments share their Source context with the
remaining statements; the executable profile chooses its own supported form. -/
theorem assignment
    {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue resolution operator rhs) :
    Statements source context rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original <;> rfl

/-- A unary assignment keeps the original suffix context. -/
theorem bitNot
    {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : AssignmentResolution}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot resolution) :
    Statements source context rest := by
  apply suffix_of_form unique typed found
  intro control final original
  rw [form] at original
  cases original <;> rfl

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
