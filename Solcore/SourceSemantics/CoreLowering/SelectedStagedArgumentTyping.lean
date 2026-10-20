import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {program : Program} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {ids : List ExpressionId} {types : List TypeSystem.Ty} {values : List Dynamic.Value}

theorem values_at (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) after) :
    Dynamic.ValuesHaveTypes context after values types ∧
      Dynamic.HeapWellTyped context after ∧ Dynamic.HeapTypesExtend before after := by
  have preserved := Staging.Recursive.SelectedPreservation.expressions selectedBodies
    runtime covers locals heap typing trace
  exact ⟨preserved.values_typed values rfl, preserved.heap_typed, preserved.heap_extends⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)
  {function : Dynamic.Closure} {parameter result : TypeSystem.Ty}

theorem closure_at (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program stages)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionsHaveTypes invocation.source context ids types)
    (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : values.length = function.parameters.length)
    (admitted : Admission bridge context reached) {size : Nat}
    (trace : Staging.Recursive.Size.Expressions program stages size invocation context
      environment before ids (.values values) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap values ∧
      Dynamic.ClosureFrame program function := by
  obtain ⟨argumentsTyped, _finalHeap, extension⟩ :=
    values_at selectedBodies runtime covers locals heap typing trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack values
  obtain ⟨raw, _rows⟩ :=
    CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
      bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨_parameters, _result, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  exact ⟨raw, signatures.trans runtime.signatures, code.owner, code,
    code.requirement_ledger.idsUnique, evidence⟩

end Solcore.SourceSemantics.CoreLowering.SelectedStagedArgumentTyping
