import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPositiveFunctionModels
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment

/-! The actual builtin codebook row and the equal second gate supply physical
arity. Original callee typing and the independent Source/native pack receipts
then recover the ordered scalar arguments at the unchanged argument post.
This is a static input producer for the original builtin application proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {mapping : LocationMap} {world : StoreTyping}

private theorem function_builtin {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    {carrier : Value} {type : Ty}
    (positive : CallableIndexedOwnedContextualCellOrigins.FunctionOrigins
      headers keys bodyRegistry faults mapping world sourceType sourceValue carrier type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world sourceType sourceValue carrier type := by
  cases positive with
  | builtin related =>
    intro function _same
    cases related with
    | prior prior =>
      cases prior with
      | prior original =>
        cases original with
        | builtin builtin => exact builtin
  | closure member => intro function impossible; cases impossible
  | global related => intro function impossible; cases impossible

private theorem builtin_own_type {sourceType : TypeSystem.Ty} {function : Dynamic.BuiltinFunction}
    {carrier : Value} {type : Ty}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      sourceType (.builtin function) carrier type) :
    CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) carrier type := by
  cases related with
  | builtin selected number descriptor typed => exact .builtin selected number descriptor typed

/-- Only the actual contextual builtin branch is inverted. Compatible raw
views retain its same compiler descriptor, carrier and typed environment. -/
theorem builtin_member {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value}
    {carrier : Value} {type : Ty}
    (represented : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world sourceType sourceValue carrier type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world
        function.id.type (.builtin function) carrier type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | function related =>
    intro function same
    cases same
    exact builtin_own_type (function_builtin related function rfl)
  | compatible _ _ ih => exact ih
  | unit | bool | word | integer | product | proxy | constructed | mappingValue =>
    intro function impossible; cases impossible
  | nil | cons | empty | entry | absent | present => trivial

private theorem native_type {function : Dynamic.BuiltinFunction} {carrier : Value} {type : Ty}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) carrier type) :
    type = CallableContract.functionType (SourceCoreInteger.builtinParameter function.id)
      (SourceCoreInteger.builtinResult function.id) := by
  generalize sourceTypeEq : function.id.type = actualSourceType at related
  cases related
  rfl

private theorem native_count (function : BuiltinFunctionId) :
    (CompatibleBuiltinMeaning.argumentTypes function).length = function.parameterTypes.length := by
  cases function <;> rfl

private theorem values_represents
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {sourceTypes : List TypeSystem.Ty} {nativeTypes : List Ty}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceTypes nativeTypes sources values) :
    ValuesRep compiled.compatible.checked registry functions mapping world
      sourceTypes sources values nativeTypes := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

section Arguments
variable {functionModel : CallableIndexedOwnedPositiveFunctionModels.Receiving headers keys bodyRegistry faults profile}
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {function : Dynamic.BuiltinFunction} {carrier : Value}
  {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
  {parameter result : TypeSystem.Ty}

/-- Every field concerns the same literal compiler, callee and ordered values.
No computation, body law, heap conversion or reached-state replacement is stored. -/
structure Rows : Prop where
  source_parameter : parameter = TypeSystem.Ty.productMany function.id.parameterTypes
  source_result : result = function.id.returnType
  original_result : compiler.original.type = function.id.returnType
  native_parameter : compiler.parameterType = SourceCoreInteger.builtinParameter function.id
  native_result : compiler.resultType = SourceCoreInteger.builtinResult function.id
  source_row : sourceTypes = function.id.parameterTypes
  native_row : compiler.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function.id
  builtin : CallableIndexedBuiltinValues.Represents compiled.indexed world
    function.id.type (.builtin function) carrier compiler.calleeCode.type
  represented : ValuesRep compiled.compatible.checked registry
    (functionModel)
    mapping world function.id.parameterTypes sources values
    (CompatibleBuiltinMeaning.argumentTypes function.id)

include compiler in
/-- Equal physical count is the actual codebook branch, independent of packed
types. Those packs only identify rows after that count has been authenticated. -/
theorem at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    {row : SourceCoreStageCodebook.Decision}
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids originalMetadata originalNode function carrier row)
    (equalCount : row.entry.parameterCount = ids.length)
    {context : SourceSemantics.Context} {calleeHeap : Dynamic.Heap}
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) (.function parameter result))
    (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world
      (.function parameter result) (.builtin function) carrier compiler.calleeCode.type)
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functionModel))
      mapping world sourceTypes (compiler.codes.map (·.type)) sources values)
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (originalResult : compiler.original.type = result) :
    Rows (functionModel := functionModel) (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (profile := profile)
      (mapping := mapping) (world := world) (function := function) (carrier := carrier)
      (sourceTypes := sourceTypes) (sources := sources) (values := values)
      (parameter := parameter) (result := result) compiler := by
  have builtin := builtin_member calleeRelated function rfl
  rcases calleeTyped.builtin_inv with ordinary | staged
  · change TypeSystem.Ty.function parameter result =
      TypeSystem.Ty.function (TypeSystem.Ty.productMany function.id.parameterTypes) function.id.returnType at ordinary
    have signature := TypeSystem.Ty.function.inj ordinary
    have nativeSignature : compiler.parameterType = SourceCoreInteger.builtinParameter function.id ∧
        compiler.resultType = SourceCoreInteger.builtinResult function.id := by
      have acceptedType := compiler.callableType
      rw [actualFunctionType] at acceptedType
      exact CallableIndexedOwnedStoredNativePackReceipts.callable_parameters
        (acceptedType.trans (native_type builtin))
    have physical : function.id.parameterTypes.length = ids.length :=
      builtinAt.parameter_count.symm.trans equalCount
    have representedCount : compiler.codes.length = sources.length := by
      simpa only [List.length_map] using represented.length.1
    have actualCount : sources.length = function.id.parameterTypes.length :=
      representedCount.symm.trans (compiler.ordered_children.1.symm.trans physical.symm)
    have sourceRow : sourceTypes = function.id.parameterTypes :=
      CallableIndexedOwnedStoredArgumentAlignment.source_rows_of_bundle
        ((CallableIndexedOwnedStoredArgumentAlignment.source_length represented).trans actualCount)
        (bundle.trans signature.1)
    have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
        SourceCoreCompatibleCatalog.packTypes (CompatibleBuiltinMeaning.argumentTypes function.id) :=
      (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
        (compiler.packedType.symm.trans
          (nativeSignature.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function.id).symm))
    have nativeRow : compiler.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function.id :=
      CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
        (represented.length.1.trans (actualCount.trans (native_count function.id).symm)) nativePacked
    have exactRows := values_represents represented
    rw [sourceRow, nativeRow] at exactRows
    exact ⟨signature.1, signature.2, originalResult.trans signature.2,
      nativeSignature.1, nativeSignature.2, sourceRow, nativeRow, builtin, exactRows⟩
  · obtain ⟨inner, impossible, _typed⟩ := staged
    cases impossible

section Caller
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
  {calleeState : callerProtocol.State index} {calleeNode : ExpressionNode}

include bridge compiler in
/-- The actual strict callee post supplies original Source typing. Only its
value-typing field is used; the incoming caller state and all arguments stay literal. -/
theorem at_callee_post
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
    {row : SourceCoreStageCodebook.Decision}
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt
      sidecar site callee ids originalMetadata originalNode function carrier row)
    (equalCount : row.entry.parameterCount = ids.length)
    (calleePost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      bridge context calleeNode.type (.value (.builtin function)) calleeState)
    (calleeFunction : calleeNode.type = .function parameter result)
    (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
      headers keys bodyRegistry registry faults profile mapping world
      calleeNode.type (.builtin function) carrier compiler.calleeCode.type)
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (functionModel))
      mapping world sourceTypes (compiler.codes.map (·.type)) sources values)
    (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (originalResult : compiler.original.type = result) :
    Rows (functionModel := functionModel) (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry)
      (registry := registry) (faults := faults) (profile := profile)
      (mapping := mapping) (world := world) (function := function) (carrier := carrier)
      (sourceTypes := sourceTypes) (sources := sources) (values := values)
      (parameter := parameter) (result := result) compiler := by
  have typed := (CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value calleePost).1
  rw [calleeFunction] at typed calleeRelated
  exact at_arguments compiler actualFunctionType builtinAt equalCount typed calleeRelated represented bundle originalResult
end Caller
end Arguments
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinArgumentRows
