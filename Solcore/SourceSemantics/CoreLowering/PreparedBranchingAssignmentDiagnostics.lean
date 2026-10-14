import Solcore.SourceSemantics.CoreLowering.AssignmentDiagnosticOrigins

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
open Core Frontend SourceInference

theorem operands {source : TypedSource} {first : Nat} {table : SourceCoreAssignmentFaultSites.Table}
    {faults : FunctionCalls.FaultRep}
    (prepared : SourceCoreAssignmentFaultSites.prepare source first = .ok table)
    (included : ∀ reason word, GenericAssignmentDiagnostics.OperandRep table reason word → faults reason word)
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution}
    {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (origin : AssignmentDiagnosticOrigins.Occurs source site assignment operator rhs)
    (profile : operator = .equal ∨ assignment.target.type = .word) :
    AssignmentOperandDiagnostics.OperandsLaw faults operator
      (GenericAssignmentDiagnostics.token table site assignment.target.root operator) := by
  have raw : operator = .equal ∨ assignment.target.type = .word ∨ assignment.target.type = .integer :=
    profile.elim Or.inl (fun word => .inr (.inl word))
  cases origin with
  | statement found form =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands_included included prepared present.1 (.statement form) raw
  | header found form member =>
    have present := lookupStatement?_sound found
    rw [← present.2]
    exact GenericAssignmentDiagnostics.prepared_operands_included included prepared present.1 (.header form member) raw

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
