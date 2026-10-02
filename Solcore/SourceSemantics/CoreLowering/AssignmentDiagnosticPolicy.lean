import Solcore.SourceSemantics.CoreLowering.GenericAssignmentReachableDiagnostics

/-! One static policy selects the original unconditional operand receipt or its
reachable form. Both preserve missing/default and uninitialized laws. The policy
contains no execution and its interpretation never enlarges the fault relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference

inductive AssignmentDiagnosticPolicy where
  | unconditional
  | reachable

namespace GenericAssignmentStatements.Head
variable {values : ValuesContext} {source : TypedSource}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}

/-- The selected assignment diagnostic receipt at one actual Head. -/
def ErrorsFor
    (head : Head values source context certificate scope administrative definitions assignment operator rhs)
    (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : Prop :=
  match policy with
  | .unconditional => head.Errors registry faults
  | .reachable => head.ReachableErrors registry faults

theorem ErrorsFor.reachable
    {head : Head values source context certificate scope administrative definitions assignment operator rhs}
    {policy : AssignmentDiagnosticPolicy} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (errors : head.ErrorsFor policy registry faults) : head.ReachableErrors registry faults := by
  cases policy with
  | unconditional => exact Errors.reachable errors
  | reachable => exact errors

end GenericAssignmentStatements.Head
end Solcore.SourceSemantics.CoreLowering
