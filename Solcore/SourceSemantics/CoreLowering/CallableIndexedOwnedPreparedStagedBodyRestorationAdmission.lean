import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyRestorationAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionBounds

/-! The same saved physical caller restoration transports a staged body
post. Successful typing uses an authentic context-support receipt. Both
fault tags retain their exact outcome and the returned pool's stable rows. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyRestorationAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedBodyRestorationAdmission (bridge)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller body : ProtectedStateTransition.Index}

/-- No stage failure is converted into a semantic failure. The body and
caller contexts stay distinct until their genuine support receipt is used. -/
theorem restore_post (saved : State headers keys caller) (reached : State headers keys body)
    (selected : Fin keys.length) {bodyContext callerContext : SourceSemantics.Context}
    {type : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (savedRows : StableRows saved)
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      bridge bodyContext type outcome reached)
    (supports : Dynamic.TypeContextSupports bodyContext callerContext)
    (restoredFrame : AdministrativePreserved caller.mapping caller.store body.mapping
      (CallableIndexedOwnedBodyRestoration.finalIndex (body := body) saved selected).store) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge callerContext type outcome
      (CallableIndexedOwnedBodyRestoration.returned saved reached selected) := by
  cases outcome with
  | value value =>
    exact CallableIndexedOwnedBodyRestorationAdmission.restore_post
      saved reached selected savedRows post supports restoredFrame
  | fault failure =>
    cases failure with
    | semantic reason =>
      exact CallableIndexedOwnedBodyRestorationAdmission.restore_fault_post
        saved reached selected savedRows restoredFrame
    | stage origin call reason =>
      exact CallableIndexedOwnedBodyRestorationAdmission.restore_rows
        saved reached selected savedRows restoredFrame

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBodyRestorationAdmission
