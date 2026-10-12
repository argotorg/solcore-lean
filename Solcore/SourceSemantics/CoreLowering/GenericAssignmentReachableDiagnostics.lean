import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead
import Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics

/-! The existing diagnostic receipt remains available unchanged. This weaker
receipt authenticates operand tokens only for a source operand failure; missing
mapping defaults retain their original law, while uninitialized projection
errors require an actual nonempty projection path. -/
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
  uninitialized : head.prepared.steps ≠ [] → ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection
  operands : AssignmentOperandDiagnostics.OperandsLaw faults operator head.invalid

theorem Errors.reachable
    {head : Head values source context certificate scope administrative definitions assignment operator rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (errors : head.Errors registry faults) : head.ReachableErrors registry faults :=
  ⟨errors.missing, fun _ => errors.uninitialized, AssignmentOperandDiagnostics.of_unconditional errors.operands⟩

theorem ReachableErrors.equal
    {head : Head values source context certificate scope administrative definitions assignment .equal rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (missing : ∀ {root resolved reason token count},
      CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
    (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection) :
    head.ReachableErrors registry faults :=
  ⟨missing, fun _ => uninitialized, AssignmentOperandDiagnostics.equal faults head.invalid⟩

/-- A plain bare write neither reads a projected leaf nor evaluates an operand
operation. Its static body needs no diagnostics for those unreachable faults. -/
theorem ReachableErrors.bare_equal
    {head : Head values source context certificate scope administrative definitions assignment .equal rhs}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (empty : head.prepared.steps = []) : head.ReachableErrors registry faults := by
  refine ⟨?_, fun nonempty => False.elim (nonempty empty), AssignmentOperandDiagnostics.equal faults head.invalid⟩
  intro root resolved reason token count fault
  rw [empty] at fault
  cases fault

end Head
end Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatements
