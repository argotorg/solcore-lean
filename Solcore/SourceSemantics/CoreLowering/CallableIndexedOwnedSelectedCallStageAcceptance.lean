import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts

/-! An actual selected guard accepts only from its independent original stage
facts or from the exact original validator success equation. Effectful callers
and runtime callers retain distinct real premises; argument and result comptime
conditions stay explicit. These finite static adapters supply only the first
native gate. IndirectApplicationValid and prepareGuard success do not imply
stage acceptance, and staged rejection is not a plain Dynamic fault. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallStageAcceptance
open Core Frontend SourceInference
open Staging.CallGuard

variable {frame : Staging.CallBoundary.Frame} {site : SourceCoreCallableContracts.Callsite}
  {call : ExpressionId} {arguments : List ExpressionId} {source : Dynamic.Value} {native : Value}
  (dispatch : CallStageBoundary.Dispatch frame site call arguments source native)

/-- The real selected accepted guard yields the exact native first decision. -/
theorem before_arguments (accepted : Staging.CallBoundary.GuardAccepts frame call arguments source)
    (unknown : Word) :
    CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none := by
  rw [site.decision_known .beforeArguments unknown dispatch.contract dispatch.row dispatch.found]
  exact SourceCoreCallableContracts.reason_accepted dispatch.row site.reasonAt .beforeArguments
    (dispatch.accepted accepted)

include dispatch in
/-- Genuine effectful caller metadata bypasses only the original first guard. -/
theorem effectful (caller : Effectful frame.stages) :
    Staging.CallBoundary.GuardAccepts frame call arguments source :=
  .contract dispatch.bound (.effectful caller)

/-- Genuine runtime caller receipts keep every original ordered argument stage
and the independent result stage check. -/
theorem runtime (caller : ¬ Effectful frame.stages)
    (argumentsPass : ArgumentsAccept frame.stages dispatch.guard.contract.stagedResult 0
      dispatch.guard.contract.parameters arguments)
    (resultPass : ResultAccepts frame.stages call dispatch.guard.contract.stagedResult) :
    Staging.CallBoundary.GuardAccepts frame call arguments source :=
  .contract dispatch.bound (.ordinary caller argumentsPass resultPass)

/-- Exact validator success for this same retained guard constructs its
independent Source acceptance. Preparing a guard alone supplies no verdict. -/
theorem of_validator
    (checked : SourceCompilationPlan.validateStagedCallableContract dispatch.guard.sidecar.caller
      dispatch.guard.node dispatch.guard.arguments dispatch.guard.contract.parameters
      dispatch.guard.contract.stagedResult dispatch.guard.contract.owner = .ok ()) :
    Staging.CallBoundary.GuardAccepts frame call arguments source := by
  have passed : dispatch.guard.decision = .ok () := dispatch.guard.exact.symm.trans checked
  have accepted := (CallStageGuard.guard_accepts_iff dispatch.guard).mp passed
  apply Staging.CallBoundary.GuardAccepts.contract dispatch.bound
  simpa only [dispatch.call_eq, dispatch.arguments_eq, ← dispatch.stages] using accepted

/-- Exact original guard success closes the native stage gate at its retained
contract word, without observing or evaluating a child expression. -/
theorem before_arguments_of_validator
    (checked : SourceCompilationPlan.validateStagedCallableContract dispatch.guard.sidecar.caller
      dispatch.guard.node dispatch.guard.arguments dispatch.guard.contract.parameters
      dispatch.guard.contract.stagedResult dispatch.guard.contract.owner = .ok ())
    (unknown : Word) :
    CallableContract.decision site.gates .beforeArguments unknown dispatch.contract = none :=
  before_arguments dispatch (of_validator dispatch checked) unknown

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallStageAcceptance
