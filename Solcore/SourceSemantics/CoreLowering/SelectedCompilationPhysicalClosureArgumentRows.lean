import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSuccessfulArgumentTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallBounds

/-! The actual selected closure and accepted physical row determine the two
ordered argument vectors independently. Raw Source typing follows the executed
successful argument trace at its reached heap. The positive contextual payload
retains the real closure Code; native bundle equality supplies no Source count.
No body or application meaning is part of this argument producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
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

local notation "functions" => CallableIndexedOwnedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

include dispatch selected count in
/-- Original binding, actual Source list length and the same selected second
row fix physical closure arity before either packed type is used. -/
theorem source_arity {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    sources.length = function.parameters.length := by
  have retained := CallableIndexedOwnedStoredIndirectCallBounds.selected_contract dispatch selected
  have physical : dispatch.row.entry.parameterCount = function.parameters.length := by
    cases dispatch.bound with
    | closure parameters _ =>
      exact (selected.parameter_count retained).trans (congrArg List.length parameters)
  exact trace.sound.length.symm.trans (count.symm.trans physical)

include bridge profile compiler reached dispatch selected count in
/-- At the actual successful argument endpoint, the original Source trace
constructs raw closure admission and its frame. The same positive payload then
constructs the retained contextual member and exact native binder arguments. -/
theorem at_arguments
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (argumentsTyped : Dynamic.ValuesHaveTypes context index.heap sources sourceTypes)
    (extension : Dynamic.HeapMetadataExtend calleeHeap index.heap)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (admitted : Admission bridge context reached)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (calleeRelated : CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry semanticFaults profile index.mapping index.world
      (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
    (represented : DataExpressionSequence.Values model index.mapping index.world
      sourceTypes (compiler.codes.map (·.type)) sources values)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment calleeHeap ids (.values sources) index.heap) :
    CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function index.heap sources ∧
    Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function ∧
    ∃ bindings parameterCore resultCore,
      CallableIndexedOwnedPhysicalClosureAssociation.StaticMember headers keys bodyRegistry semanticFaults
        index.mapping index.world function carrier bindings parameterCore resultCore ∧
      compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore ∧
      CallableIndexedParameterMeaning.Arguments model index.mapping index.world bindings sources values := by
  have arity := source_arity dispatch selected count trace
  obtain ⟨packed, packing⟩ := Dynamic.ValuesPack.exists_pack sources
  obtain ⟨raw, _rows⟩ := CallableIndexedOwnedStoredClosureSourceArguments.after_argument_extension
    bridge reached runtime admitted calleeTyped extension argumentsTyped packing bundle arity
  obtain ⟨_parameters, _result, signatures, code, evidence, _captures⟩ := calleeTyped.closure_function_inv
  have valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function :=
    ⟨signatures.trans runtime.signatures, code.owner, code, code.requirement_ledger.idsUnique, evidence⟩
  obtain ⟨bindings, parameterCore, resultCore, member, nativeType⟩ :=
    CallableIndexedOwnedPhysicalCellOrigins.PayloadOrigins.closure_member profile calleeRelated function rfl
  have sameTypes := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
    ((actualFunctionType ▸ compiler.callableType).trans nativeType)
  have nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
      (compiler.packedType.symm.trans (sameTypes.1.trans (member.forget.parameter_core profile)))
  obtain ⟨parameters, _result, _signatures, _code, _evidence, _captures⟩ := calleeTyped.closure_function_inv
  have sourceBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
    rw [member.forget.source_binders]
    exact bundle.trans parameters
  have bindingArity : sources.length = bindings.length := by
    have retainedBinders : bindings.length = function.parameters.length := by
      simpa only [List.length_map] using congrArg List.length member.forget.source_binders
    exact arity.trans retainedBinders.symm
  exact ⟨raw, valid, bindings, parameterCore, resultCore, member, sameTypes.1, sameTypes.2,
    CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles bindings represented
      bindingArity sourceBundle nativeBundle⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureArgumentRows
