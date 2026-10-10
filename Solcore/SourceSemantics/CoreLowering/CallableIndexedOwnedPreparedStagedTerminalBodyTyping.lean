import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaSourceAdmission

/-! Original body typing selects the retained terminal expression and its
declared result type. This uses Source statement rules and full occurrence
identity, independently of erased native types or an execution outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping
open Frontend SourceInference
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

private theorem returning_child {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (typed : StatementHasType source control context id final facts) :
    ExpressionHasType source context expression control.returnType := by
  have shape := statement_shape unique contains form
  clear contains form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all

private theorem tail_child {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression false)
    (typed : StatementHasType source control context id final facts) :
    ∃ type, ExpressionHasType source context expression type ∧
      facts = { type, hasValue := true, sawReturn := false, control := .ordinary type } := by
  have shape := statement_shape unique contains form
  clear contains form
  cases typed <;> have actualForm := shape _ (by assumption) <;> simp_all
  exact ⟨_, by assumption, rfl, rfl⟩

/-- The supported terminal form and complete original body typing determine
its used expression type and actual lookup occurrence. -/
theorem child_typed {invocation : Staging.Recursive.Scope}
    {context final : SourceSemantics.Context} {expression : ExpressionId}
    {statements : List StatementId} {expected : TypeSystem.Ty} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression statements)
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context statements final facts)
    (completes : BodyCompletes expected facts) :
    ∃ node, invocation.source.lookupExpression? expression = some node ∧
      node.type = expected ∧ ExpressionHasType invocation.source context expression node.type := by
  have expressionTyped : ExpressionHasType invocation.source context expression expected := by
    cases head with
    | returning rest contains form =>
      cases typed with
      | singleton first => exact returning_child unique contains form first
      | cons first _tail => exact returning_child unique contains form first
    | tail contains form =>
      cases typed with
      | singleton first =>
        obtain ⟨type, child, sameFacts⟩ := tail_child unique contains form first
        rw [sameFacts] at completes
        have sameType : type = expected := by
          simpa [BodyCompletes, BodyFacts.singleton, ControlSummary.ordinary] using completes
        exact sameType ▸ child
  obtain ⟨node, contains, sameType⟩ := expressionTyped.stored_type
  exact ⟨node, lookupExpression?_complete unique contains, sameType, sameType ▸ expressionTyped⟩

/-- The real original lambda frame supplies complete body typing at the
actual parameter context before selecting the terminal child. -/
theorem at_parameters {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {invocation : Staging.Recursive.Scope} {expression : ExpressionId}
    (frame : Dynamic.ClosureFrame program function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (source : invocation.source = function.source)
    (head : Head invocation expression function.body) :
    ∃ node, invocation.source.lookupExpression? expression = some node ∧
      node.type = function.resultType ∧ ExpressionHasType invocation.source context expression node.type := by
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
  have unique : NodeOccurrencesUnique invocation.source := by
    rw [source]
    exact frame.code.graph.nodeOccurrencesUnique
  rw [← source] at typed
  exact child_typed unique head typed completes

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping
