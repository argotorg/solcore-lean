import Solcore.SourceSemantics.CoreLowering.SelectedCompilationControlNoEscape
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure
import Solcore.SourceSemantics.Staging.RecursiveControlTransferFacts

/-! The original selected body typing rules close staged function control.
Only breaking and continuing need erasure; a stage stop keeps its own origin. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.TypedControlBoundary
open Frontend SourceInference

/-- The actual function trace and its original zero-depth typing exclude both
loop transfers without a validity assumption on other program bodies. -/
theorem function {program : Program} {registry : Registry} {scope : Scope}
    (unique : NodeOccurrencesUnique scope.source)
    {control : ControlContext} {context staticFinal : Context}
    {ids : List StatementId} {facts : BodyFacts}
    (typing : StatementsHaveType scope.source control context ids staticFinal facts)
    (depth : control.loopDepth = 0)
    {runtimeContext finalContext : Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : BodyOutcome}
    (trace : Statements program registry scope runtimeContext environment before
      ids finalContext outcome after) : outcome.NoEscapedControl := by
  constructor
  · intro escaped same
    subst outcome
    exact (CoreLowering.SelectedCompilationControlNoEscape.function unique typing depth
      trace.breaking_plain).1 escaped rfl
  · intro escaped same
    subst outcome
    exact (CoreLowering.SelectedCompilationControlNoEscape.function unique typing depth
      trace.continuing_plain).2 escaped rfl

/-- At a typed function boundary, a fault result comes from its actual fault
trace. Loop transfers have already been excluded from the selected body. -/
theorem body_fault {type : TypeSystem.Ty} {outcome : BodyOutcome} {failure : Failure}
    (closed : outcome.NoEscapedControl)
    (rule : BodyResult type outcome (.fault failure)) : outcome = .fault failure := by
  cases rule with
  | fault => rfl
  | breaking => exact (closed.1 _ rfl).elim
  | continuing => exact (closed.2 _ rfl).elim

end Solcore.SourceSemantics.Staging.Recursive.TypedControlBoundary
