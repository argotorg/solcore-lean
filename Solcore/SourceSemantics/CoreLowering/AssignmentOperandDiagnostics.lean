import Solcore.SourceSemantics.CoreLowering.FunctionCalls
import Solcore.SourceSemantics.Dynamic.Fault

/-! Assignment operand tokens are required only when the independent source
operand relation can fail. Plain assignment always accepts its RHS, so no
diagnostic entry is needed for its unused native operand token. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
open Core Frontend

def OperandsLaw (faults : FunctionCalls.FaultRep) (operator : Syntax.ValueAssignOp)
    (token : Word) : Prop :=
  ∀ previous right, Dynamic.AssignmentOperandsInvalid operator previous right →
    faults (.invalidAssignmentOperands operator) token

theorem invalid_not_equal {operator : Syntax.ValueAssignOp}
    {previous : Option Dynamic.Value} {right : Dynamic.Value}
    (invalid : Dynamic.AssignmentOperandsInvalid operator previous right) : operator ≠ .equal := by
  cases invalid with
  | uninitialized different => exact different
  | compound corresponds _ => cases corresponds <;> intro same <;> cases same

theorem equal (faults : FunctionCalls.FaultRep) (token : Word) :
    OperandsLaw faults .equal token := by
  intro previous right invalid
  exact (invalid_not_equal invalid rfl).elim

theorem of_unconditional {faults : FunctionCalls.FaultRep} {operator : Syntax.ValueAssignOp}
    {token : Word} (interpreted : faults (.invalidAssignmentOperands operator) token) :
    OperandsLaw faults operator token := by
  intro _ _ _
  exact interpreted

theorem of_not_equal {faults : FunctionCalls.FaultRep} {operator : Syntax.ValueAssignOp}
    {token : Word} (interpreted : operator ≠ .equal → faults (.invalidAssignmentOperands operator) token) :
    OperandsLaw faults operator token := by
  intro previous right invalid
  exact interpreted (invalid_not_equal invalid)

end Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
