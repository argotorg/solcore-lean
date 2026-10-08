import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedObservedGeneralCallee

/-! Independent raw Source argument typing is transported at the actual
argument post into the selected closure context. The original packed-value and
arity rules recover the real Source binder row. Native parameter vectors do
not supply Source types or deep heap admission. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission

/-- All facts refer to the same actual after-argument Source heap. Captured
locals are checked there, independently of immutable compiler history. -/
structure SourceArguments (function : Dynamic.Closure) (heap : Dynamic.Heap)
    (arguments : List Dynamic.Value) : Prop where
  heaps : Dynamic.HeapWellTyped function.context heap
  arguments : Dynamic.ValuesHaveTypes function.context heap arguments
    (function.parameters.map (fun binder => binder.scheme.body))
  captures : Dynamic.EnvironmentAgrees heap function.context.locals function.captured
  code : Dynamic.ClosureCodeValid function.context function
  covers : function.evidence.Covers function.context

variable {program : Program} {context : SourceSemantics.Context} {source : TypedSource}
  {function : Dynamic.Closure} {heap : Dynamic.Heap}
  {parameter result : TypeSystem.Ty} {arguments : List Dynamic.Value}
  {types : List TypeSystem.Ty} {packed : Dynamic.Value}

/-- Actual Source callee typing fixes its exact binder bundle. Genuine packed
argument typing and matching actual arity then recover its raw parameter row.
Closed-context transport keeps this heap and these values unchanged. -/
theorem at_arguments (runtime : Dynamic.SourceRuntimeValid program context source)
    (calleeTyped : Dynamic.ValueHasType context heap (.closure function) (.function parameter result))
    (heapTyped : Dynamic.HeapWellTyped context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : arguments.length = function.parameters.length) : SourceArguments function heap arguments := by
  obtain ⟨parameters, _result, signatures, code, covers, captures⟩ := calleeTyped.closure_function_inv
  have packedTyped : Dynamic.ValueHasType context heap packed
      (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) := by
    rw [← parameters, ← bundle]
    exact packing.hasType argumentsTyped
  have closureHeap := heapTyped.transportClosed signatures runtime.closed code.closed
    runtime.variables_closed code.residual_variables_open
  have closurePacked := packedTyped.transportClosed signatures runtime.closed code.closed
    runtime.variables_closed code.residual_variables_open
  have closureArguments := packing.unpackTypes closurePacked (by simpa using arity)
  exact ⟨closureHeap, closureArguments, captures, code, covers⟩

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- The genuine admitted after-argument state supplies both deep Source heap
validity and every current owned row. Neither is replaced by a captured row or
an earlier callee state. The arity/bundle remain authentic Source call facts. -/
theorem at_admitted_arguments (runtime : Dynamic.SourceRuntimeValid program context source)
    (admitted : Admission bridge context reached)
    (calleeTyped : Dynamic.ValueHasType context index.heap (.closure function) (.function parameter result))
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : arguments.length = function.parameters.length) :
    SourceArguments function index.heap arguments ∧
    CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached) :=
  ⟨at_arguments runtime calleeTyped admitted.heap argumentsTyped packing bundle arity, admitted.rows⟩

/-- The actual argument trace's Source type extension carries callee typing
from its own success post to the later argument post. All deep heap and owned
row admission is still taken from the actual later state. -/
theorem after_argument_extension {calleeHeap : Dynamic.Heap}
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (admitted : Admission bridge context reached)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (extension : Dynamic.HeapTypesExtend calleeHeap index.heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap arguments types)
    (packing : Dynamic.ValuesPack arguments packed)
    (bundle : TypeSystem.Ty.productMany types = parameter)
    (arity : arguments.length = function.parameters.length) :
    SourceArguments function index.heap arguments ∧
    CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached) :=
  at_admitted_arguments bridge reached runtime admitted (calleeTyped.mono extension)
    argumentsTyped packing bundle arity

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureSourceArguments
