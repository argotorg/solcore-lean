import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Original Source for typing determines each header context. Successful
initialization identifies the reached context directly from its binder receipts;
no execution preservation law or program well-formedness premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping
open Frontend SourceInference Staging.Recursive
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body) : Statements source context rest := by
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
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body) :
    ∃ control loopContext postContext bodyFinal bodyFacts,
      ForItemsHaveType source control context initial loopContext ∧
      ExpressionHasType source loopContext condition .bool ∧
      StatementsHaveType source control.enterLoop loopContext body bodyFinal bodyFacts ∧
      ForItemsHaveType source control.enterLoop loopContext post postContext :=
  ProtectedStateImperativeTypedSourceSites.for_loop unique
    (ProtectedStateImperativeTypedSourceSites.head typed) found form

theorem initial_context {program : Program} {registry : Registry} {invocation : Scope}
    {control : ControlContext} {context staticFinal runtimeFinal : SourceSemantics.Context}
    {environment returned : Dynamic.Environment} {before after : Dynamic.Heap}
    {items : List ForItemForm} {size : Nat}
    (typed : ForItemsHaveType invocation.source control context items staticFinal)
    (trace : Size.ForItems program registry size invocation context environment before items runtimeFinal (.done returned) after) :
    runtimeFinal = staticFinal := by
  induction size using Nat.strongRecOn generalizing context staticFinal runtimeFinal environment returned before after items with
  | ind size ih =>
    cases trace with
    | empty => cases typed; rfl
    | absent mono extended allocated next =>
      cases typed with
      | cons head tail =>
        cases head with
        | letUninitialized _ _ staticExtended =>
          cases Dynamic.BinderExtends.functional extended staticExtended
          exact ih _ (Size.child_lt_stepSize (by simp)) tail next
    | initialized mono extended child allocated next =>
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized _ _ _ staticExtended =>
          cases Dynamic.BinderExtends.functional extended staticExtended
          exact ih _ (Size.child_lt_stepSize (by simp)) tail next
        | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
    | expression child next | assignment _ child _ next | bitNot _ _ next
    | projectedAssignment _ _ _ child _ next | projectedBitNot _ child _ _ next =>
      cases typed with
      | cons head tail =>
        cases head
        exact ih _ (Size.child_lt_stepSize (by simp)) tail next

theorem children_at_initial {program : Program} {registry : Registry} {invocation : Scope}
    {context loopContext : SourceSemantics.Context} {environment loopEnvironment : Dynamic.Environment}
    {before initialized : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId} {size : Nat}
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : Statements invocation.source context (id :: rest))
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body)
    (trace : Size.ForItems program registry size invocation context environment before initial loopContext (.done loopEnvironment) initialized) :
    ∃ control postContext bodyFinal bodyFacts,
      ForItemsHaveType invocation.source control context initial loopContext ∧
      ExpressionHasType invocation.source loopContext condition .bool ∧
      StatementsHaveType invocation.source control.enterLoop loopContext body bodyFinal bodyFacts ∧
      ForItemsHaveType invocation.source control.enterLoop loopContext post postContext := by
  obtain ⟨control, staticLoop, postContext, bodyFinal, bodyFacts, initialTyped, conditionTyped, bodyTyped, postTyped⟩ :=
    children unique typed found form
  cases initial_context initialTyped trace
  exact ⟨control, postContext, bodyFinal, bodyFacts, initialTyped, conditionTyped, bodyTyped, postTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping
