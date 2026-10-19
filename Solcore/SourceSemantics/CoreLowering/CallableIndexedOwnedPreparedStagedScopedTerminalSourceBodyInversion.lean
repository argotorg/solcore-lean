import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedTerminalStatements

/-! A supported terminal Head selects the actual expression child of a
staged Source statement trace. The real Source grade and both failure tags
are retained before applying the strict expression induction hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
open Frontend SourceInference
open Staging.Recursive
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head control)

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
theorem child_of_body {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {expression : ExpressionId} {statements : List StatementId}
    {size : Nat} {bodyOutcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression mode statements)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      statements finalContext bodyOutcome after) :
    ∃ childSize outcome,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ bodyOutcome = control outcome ∧
      Size.Expression program registry childSize invocation context environment before
        expression outcome after := by
  cases head with
  | returning rest contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | breaking actual same | continuing actual same =>
        cases (shape actual).symm.trans same
    | forInitializerFault actual form _ | forReturned actual form _ _ | forFault actual form _ _
    | forFallthrough actual form _ _ _
    | matchBreaking actual form _ | matchContinuing actual form _
  | matchReturned actual form _ | matchFault actual form _ | matchFallthrough actual form _ _
    | blockBreaking actual form _ | blockContinuing actual form _
  | blockReturned actual form _ | blockFault actual form _ | blockFallthrough actual form _ _
    | whileReturned actual form _ | whileFault actual form _ | whileFallthrough actual form _ _
    | ifConditionFault actual form _ | ifBreaking actual form _ _ | ifContinuing actual form _ _
  | ifReturned actual form _ _ | ifFault actual form _ _
    | ifFallthrough actual form _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
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
    | discardValue actual form child next
    | discard actual form child next =>
      have same := shape actual
      rw [form] at same
      cases same
    | expressionFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | letGeneralized actual form _ _ _ _ _
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
    | bitNotProjected actual form _ _ _ _ _
    | bitNotProjectedRootFault actual form _ _
    | bitNotProjectedKeysFault actual form _ _ _
    | bitNotProjectedGetterFault actual form _ _ _
    | bitNotBare actual form _ _ _ | bitNotBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignProjected actual form _ _ _ _ _ _
    | assignProjectedRootFault actual form _ _
    | assignProjectedKeysFault actual form _ _ _
    | assignProjectedGetterFault actual form _ _ _
    | assignProjectedRhsFault actual form _ _ _ _
    | assignProjectedWriteFault actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBare actual form snapshot child write next =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareOperands actual form _ _ _ _ _ _ _ | assignBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareUnbound actual form bare missing =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareDangling actual form bare lookup missing =>
      have same := shape actual
      rw [form] at same
      cases same
  | tail contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | breaking actual same | continuing actual same =>
        cases (shape actual).symm.trans same
    | forInitializerFault actual form _ | forReturned actual form _ _ | forFault actual form _ _
    | forFallthrough actual form _ _ _
    | matchBreaking actual form _ | matchContinuing actual form _
  | matchReturned actual form _ | matchFault actual form _ | matchFallthrough actual form _ _
    | blockBreaking actual form _ | blockContinuing actual form _
  | blockReturned actual form _ | blockFault actual form _ | blockFallthrough actual form _ _
    | whileReturned actual form _ | whileFault actual form _ | whileFallthrough actual form _ _
    | ifConditionFault actual form _ | ifBreaking actual form _ _ | ifContinuing actual form _ _
  | ifReturned actual form _ _ | ifFault actual form _ _
    | ifFallthrough actual form _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
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
    | letGeneralized actual form _ _ _ _ _
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
    | bitNotProjected actual form _ _ _ _ _
    | bitNotProjectedRootFault actual form _ _
    | bitNotProjectedKeysFault actual form _ _ _
    | bitNotProjectedGetterFault actual form _ _ _
    | bitNotBare actual form _ _ _ | bitNotBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignProjected actual form _ _ _ _ _ _
    | assignProjectedRootFault actual form _ _
    | assignProjectedKeysFault actual form _ _ _
    | assignProjectedGetterFault actual form _ _ _
    | assignProjectedRhsFault actual form _ _ _ _
    | assignProjectedWriteFault actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBare actual form snapshot child write next =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareOperands actual form _ _ _ _ _ _ _ | assignBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareUnbound actual form bare missing =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareDangling actual form bare lookup missing =>
      have same := shape actual
      rw [form] at same
      cases same

/-- A terminal body propagates the exact Source expression outcome. -/
theorem result_of_control {type : TypeSystem.Ty} {child result : Outcome}
    (matched : BodyResult type (control child) result) : result = child := by
  cases child <;> cases matched <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
