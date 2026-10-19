import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedArgumentRows
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureArgumentRows

/-! Actual successful argument rows are aligned with the materialized closure.
The selected physical count supplies Source arity independently of packed types. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {environment : Dynamic.Environment}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {function : Dynamic.Closure} {carrier : Value} {parameter result : TypeSystem.Ty}
  {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
  {calleeHeap : Dynamic.Heap} {index : ProtectedStateTransition.Index}
  (reached : callerProtocol.State index)
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar)
    site site.call ids (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

include bridge profile compiler reached dispatch selected count in
theorem at_arguments
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap sources sourceTypes)
    (extension : Dynamic.HeapMetadataExtend calleeHeap index.heap)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (admitted : Admission bridge context reached)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (calleeRelated : GenericHeap.PayloadModel.Represents model index.mapping index.world
      (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
    (member : GeneralizedLocalMaterializedAssociation.Association compiled index.mapping index.world
      function carrier bindings parameterCore resultCore)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) sources values)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap sources ∧
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function ∧
    compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore ∧
    CallableIndexedParameterMeaning.Arguments model index.mapping index.world bindings sources values := by
  have arity := SelectedCompilationPhysicalClosureArgumentRows.source_arity dispatch selected count trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
  obtain ⟨raw, _rows⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨parameters, sourceResult, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  have valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, evidence⟩
  have nativeType : compiler.calleeCode.type = CallableContract.functionType parameterCore resultCore :=
    (GenericHeap.PayloadModel.runtime_hasType model calleeRelated).type_eq.symm.trans member.runtime_hasType.type_eq
  have sameTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    ((actualFunctionType ▸ compiler.callableType).trans nativeType)
  have nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) = parameterCore :=
    (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans sameTypes.1)
  exact ⟨raw, valid, sameTypes.1, sameTypes.2,
    GeneralizedLocalMaterializedArgumentRows.arguments member valid profile represented arity
      (bundle.trans parameters) nativeBundle⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeIndirectApplicationArguments
