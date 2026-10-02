import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead
import Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics

/-! The existing diagnostic receipt remains available unchanged. This weaker
receipt authenticates operand tokens only for a source operand failure; missing
mapping defaults and uninitialized place errors retain their original laws. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
open Core Frontend SourceInference

namespace Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

structure ReachableErrors (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) : Prop where
  missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token
  uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid

theorem Errors.reachable
    {head : Head values source context certificate scope administrative definitions assignment operator rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (errors : head.Errors registry faults) : head.ReachableErrors registry faults :=
  ⟨errors.missing, errors.uninitialized, AssignmentOperandDiagnostics.of_unconditional errors.operands⟩

theorem ReachableErrors.equal
    {head : Head values source context certificate scope administrative definitions assignment .equal rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (missing : ∀ {root resolved reason token count},
      CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
    (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection) :
    head.ReachableErrors registry faults :=
  ⟨missing, uninitialized, AssignmentOperandDiagnostics.equal faults head.invalid⟩

end Head
end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
