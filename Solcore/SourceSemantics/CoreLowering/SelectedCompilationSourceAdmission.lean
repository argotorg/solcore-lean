import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission (Admission)
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol}
  {context : SourceSemantics.Context}

/-- Concrete successful preservation supplies admission at the actual reached
state. Faults retain their own endpoint histories without asserting success. -/
theorem after_expression_sized_of_preserved {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (_trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (preserved : ∀ value, outcome = .value value →
      Dynamic.ExpressionEvaluationPreserved context initial.heap reached.heap value type)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  have rows := StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame
  cases outcome with
  | value value =>
    refine ⟨rows, ?_⟩
    intro actual same
    cases same
    have exactResult := preserved value rfl
    exact ⟨exactResult.value_typed, exactResult.heap_typed⟩
  | fault failure =>
    cases failure with
    | semantic reason => exact ⟨rows, by intro value impossible; cases impossible⟩
    | stage origin call reason => exact rows

/-- The exact caller relation and state are unchanged when adding admission. -/
theorem after_related_expression_sized_of_preserved
    {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (related : callerProtocol.Relates first last)
    (admitted : Admission bridge context first)
    {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Staging.Recursive.Outcome} {size : Nat}
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      initial.heap id outcome reached.heap)
    (preserved : ∀ value, outcome = .value value →
      Dynamic.ExpressionEvaluationPreserved context initial.heap reached.heap value type)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    callerProtocol.Relates first last ∧ PostAdmission bridge context type outcome last :=
  ⟨related, after_expression_sized_of_preserved first last admitted trace preserved frame⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds
