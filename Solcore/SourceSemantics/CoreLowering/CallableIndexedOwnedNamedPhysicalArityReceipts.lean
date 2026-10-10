import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts

/-! Actual named metadata identifies the full Source parameter list of the
selected Header. The physical count comes from the authenticated codebook and
its original guard. This does not infer arity from a packed native type or
establish the independent first-stage guard decision. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalArityReceipts
open Core Frontend SourceInference SourceCoreStageContracts
open CallableIndexedOwnedFunctionValues

section Named
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {source : Dynamic.GlobalFunction} {contract : CallContractCertificates.SourceContract}

/-- The real matcher and selected named factory recover the same ordered
binders, including their Source flags and schemes. -/
theorem bound_parameters (sourceAt : NamedSourceAt header rawD source)
    (bound : CallableLedger.Binds compiled.indexed.base.plan (.global source) contract) :
    contract.parameters = header.function.parameters := by
  have target : SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      source.instantiation = .ok header.named.signature.key := by
    rw [sourceAt.retained]
    change SourceCompilationPlan.exactInstantiationKey compiled.indexed.base.plan
      (CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation header.named.specialized)) = _
    rw [CallableNamedReversal.target_reverse]
    exact sourceAt.row.target
  cases bound with
  | named selected prepared =>
    have same := Except.ok.inj (selected.symm.trans target)
    cases same
    obtain ⟨receipt⟩ := CallContractCertificates.named_of_accepted prepared
    have sourceEq := sourceAt.sourceOrigin.source receipt.prepared
    simp only [EmptySourceSubstitution.source] at sourceEq
    exact receipt.parameters.trans ((congrArg TypedSource.inputs sourceEq).symm.trans
      (header.inputs.trans header.parameters.symm))
end Named

section Selected
variable {sidecar : Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee call : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {node : ExpressionNode}
  {source : Dynamic.Value} {carrier : Value}

/-- The original generated guard identifies the selected entry's retained
contract. Builtin rows cannot have this user dispatch attachment. -/
theorem dispatch_parameter_count
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) site call arguments source carrier)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar site callee arguments metadata node dispatch.row) :
    dispatch.row.entry.parameterCount = dispatch.guard.contract.parameters.length := by
  cases retained : dispatch.row.entry.contract with
  | none =>
    have noGuard := selected.generated.builtin retained
    have impossible := dispatch.attached.symm.trans noGuard
    cases impossible
  | some contract =>
    obtain ⟨guard, prepared, attached, _⟩ := selected.generated.user contract retained
    have same := Option.some.inj (attached.symm.trans dispatch.attached)
    cases same
    obtain ⟨receipt⟩ := CallContractCertificates.guard_of_accepted prepared
    rw [receipt.contract_eq]
    exact selected.parameter_count retained
end Selected

section Actual
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {header : Header compiled program} {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {source : Dynamic.GlobalFunction} {sidecar : Sidecar}
  {site : SourceCoreCallableContracts.Callsite} {callee : ExpressionId}
  {arguments : List ExpressionId} {metadata : IndirectCallResolution}
  {node : ExpressionNode} {carrier : Value}

/-- The same public caller sidecar, selected row and actual named value supply
the physical Header count. No count equality is a premise. -/
theorem named_parameter_count (sourceAt : NamedSourceAt header rawD source)
    (caller : prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call arguments (.global source) carrier)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar site callee arguments metadata node dispatch.row) :
    dispatch.row.entry.parameterCount = header.function.parameters.length := by
  have samePlan := (CallContractCertificates.sidecar_of_accepted caller).1
  have bound : CallableLedger.Binds compiled.indexed.base.plan (.global source)
      ⟨dispatch.guard.contract.parameters, dispatch.guard.contract.stagedResult⟩ := by
    simpa only [CallableLedger.frame, samePlan] using dispatch.bound
  exact (dispatch_parameter_count dispatch selected).trans
    (congrArg List.length (bound_parameters sourceAt bound))

/-- Genuine Source arity closes the second gate. The first stage gate remains
the original independent decision. -/
theorem before_application (sourceAt : NamedSourceAt header rawD source)
    (caller : prepareSidecar compiled.indexed.base.plan site.caller = .ok sidecar)
    (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
      site site.call arguments (.global source) carrier)
    (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar site callee arguments metadata node dispatch.row)
    (arity : header.function.parameters.length = arguments.length) (unknown : Word) :
    CallableContract.decision site.gates .beforeApplication unknown dispatch.row.entry.id = none :=
  selected.before_application ((named_parameter_count sourceAt caller dispatch selected).trans arity) unknown
end Actual
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalArityReceipts
