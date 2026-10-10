import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalArityReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds

/-! An accepted second gate recovers physical arity from its actual selected
codebook row. Closure and named parameter counts use original contract binding.
Packed Source or native types are not used to recover list lengths. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)

section Row
variable {sidecar : SourceCoreStageContracts.Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {row : SourceCoreStageCodebook.Decision} {contract unknown : Word}

/-- The original selected decision, rather than the callee's type, fixes this
accepted physical argument count. Unknown descriptors cannot supply it. -/
theorem selected_count
    (selected : Selected sidecar site callee ids metadata node row)
    (found : site.rowAt? contract = some row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown contract = none) :
    row.entry.parameterCount = ids.length := by
  rw [site.decision_known .beforeApplication unknown contract row found] at accepted
  by_cases same : row.entry.parameterCount = row.argumentCount
  · exact same.trans selected.argument_count
  · have rejected := SourceCoreCallableContracts.reason_rejected row site.reasonAt
      .beforeApplication _ (row.afterArguments_mismatch same)
    rw [rejected] at accepted
    cases accepted
end Row

section Closure
variable {sidecar : SourceCoreStageContracts.Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {function : Dynamic.Closure} {native : Value} {unknown : Word}

/-- The real closure binding identifies the retained contract's ordered
parameters; successful gate selection then supplies their physical count. -/
theorem closure_count
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.closure function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    function.parameters.length = ids.length := by
  have retained := CallableIndexedOwnedStoredIndirectCallBounds.selected_contract dispatch selected
  have count : dispatch.row.entry.parameterCount = function.parameters.length := by
    cases dispatch.bound with
    | closure parameters _ =>
      exact (selected.parameter_count retained).trans (congrArg List.length parameters)
  exact count.symm.trans (selected_count selected dispatch.found accepted)
end Closure

section Named
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {function : Dynamic.GlobalFunction} {sidecar : SourceCoreStageContracts.Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
  {native : Value} {unknown : Word}

/-- Full named Source authority and the same caller preparation identify the
actual Header parameters before the accepted gate recovers their length. -/
theorem named_count
    (sourceAt : NamedSourceAt header rawD function)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call ids (.global function) native)
    (selected : Selected sidecar site callee ids metadata node dispatch.row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown dispatch.contract = none) :
    header.function.parameters.length = ids.length :=
  (CallableIndexedOwnedNamedPhysicalArityReceipts.named_parameter_count sourceAt caller dispatch selected).symm.trans
    (selected_count selected dispatch.found accepted)
end Named
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
