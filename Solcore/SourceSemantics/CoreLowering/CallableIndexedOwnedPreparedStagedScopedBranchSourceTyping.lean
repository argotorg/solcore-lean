import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementMeaning
import Solcore.SourceSemantics.Staging.RecursiveTraceSize
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure

/-! A branch restores its original lexical context for the suffix. Static
stopping is applied only to the independently erased, actual arm execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
open Frontend SourceInference Staging.Recursive
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
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
      cases formTyped <;> exact ⟨control, final, _, tail⟩

theorem condition {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {test : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen test thenBody elseBody) :
    ExpressionHasType source context test .bool := by
  obtain ⟨control, final, facts, head⟩ := ProtectedStateImperativeTypedSourceSites.head typed
  obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
  have same : actual = node := Option.some.inj
    ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  rw [form] at formTyped
  cases formTyped <;> assumption

theorem stopped_not_fallthrough {program : Program} {registry : Registry}
    {size : Nat} {invocation : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment finalEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    {statements : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (stopped : GenericLexicalStatements.Stopped invocation.source statements)
    (trace : Size.StatementsIn program registry false size invocation context environment before
      statements finalContext (.fallthrough finalEnvironment) after) : False := by
  have terminal := stopped.terminates unique false trace.sound.fallthrough_scoped
  cases terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
