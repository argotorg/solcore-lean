import Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt

/-! The accepted compiler action supplies the complete bare bit-not head.
Its original target equality and independent Source typing determine the
writable runtime local, without equating the two Source records. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
open Core Frontend SourceInference

variable {policy : SourceCoreLoops.Policy} {fuel : Nat} {compilerSource source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {site : SourceCoreElaboration.ErrorSite}
  {assignment : AssignmentResolution} {output : Ty} {next code : Expr}
  {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context}

/-- The actual compiler target and typed runtime target identify the same
ordinary writable local, even when their surrounding requirement metadata differs. -/
def Receipt.head
    (receipt : Receipt policy fuel compilerSource scope site assignment output next reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    (typed : SourceBitNotAssignmentValid source context assignment) :
    CompatibleBitNotStatements.Head context scope assignment where
  prepared := receipt.place
  index := receipt.index
  invalid := receipt.invalidUnary site assignment.target.root
  bare := receipt.bare
  layout := receipt.layout
  slot := receipt.slot
  writable := by
    rw [receipt.rootType, targetType]
    cases typed with
    | intro target _ =>
      cases target with
      | intro writable projections stored =>
        rw [receipt.bare] at projections
        cases projections
        simpa only [stored] using writable
  profile := .inl (by rw [receipt.rawType, receipt.sourceProfile]; rfl)

theorem Receipt.head_emitted
    (receipt : Receipt policy fuel compilerSource scope site assignment output next reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    (typed : SourceBitNotAssignmentValid source context assignment) :
    code = (receipt.head targetType typed).emit next output :=
  receipt.emitted

theorem Receipt.head_errors
    (receipt : Receipt policy fuel compilerSource scope site assignment output next reasonAt code)
    (targetType : receipt.binder.scheme.body = assignment.target.type)
    (typed : SourceBitNotAssignmentValid source context assignment)
    {faults : FunctionCalls.FaultRep}
    (diagnostic : faults (.invalidUnaryOperand .bitNot)
      (receipt.invalidUnary site assignment.target.root)) :
    (receipt.head targetType typed).Errors faults :=
  diagnostic

end Solcore.SourceSemantics.CoreLowering.AcceptedBareBitNotReceipt
