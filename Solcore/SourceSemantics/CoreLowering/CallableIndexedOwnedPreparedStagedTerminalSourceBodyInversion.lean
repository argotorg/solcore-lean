import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements

/-! A supported terminal Head selects the actual expression child of a
staged Source statement trace. The real Source grade and both failure tags
are retained before applying the strict expression induction hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
open Frontend SourceInference
open Staging.Recursive
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

/-- Neither a completed body law nor a separate child trace is an input.
The literal Source constructor selects its one used child. -/
theorem child_of_body {program : Program} {registry : Registry} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {expression : ExpressionId} {statements : List StatementId}
    {size : Nat} {bodyOutcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression statements)
    (trace : Size.Statements program registry size invocation context environment before
      statements finalContext bodyOutcome after) :
    ∃ childSize outcome,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ bodyOutcome = control outcome ∧
      Size.Expression program registry childSize invocation context environment before
        expression outcome after := by
  cases head with
  | returning rest contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | returnUnit actual form =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnValue actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | returnFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | tail actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | discard actual form child next =>
      have same := shape actual
      rw [form] at same
      cases same
    | expressionFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | letUninitialized actual form mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letInitialized actual form child mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letFault actual form mono child =>
      have same := shape actual
      rw [form] at same
      cases same
  | tail contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | returnUnit actual form =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnValue actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | tail actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | discard actual form child next =>
      have same := shape actual
      rw [form] at same
      cases same
    | expressionFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | letUninitialized actual form mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letInitialized actual form child mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letFault actual form mono child =>
      have same := shape actual
      rw [form] at same
      cases same

/-- A terminal body propagates the exact Source expression outcome. -/
theorem result_of_control {type : TypeSystem.Ty} {child result : Outcome}
    (matched : BodyResult type (control child) result) : result = child := by
  cases child <;> cases matched <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
