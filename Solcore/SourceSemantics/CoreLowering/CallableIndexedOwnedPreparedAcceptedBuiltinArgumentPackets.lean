import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPositiveFunctionOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAcceptedIndirectPhysicalArity
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceTypeRows
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment

/-! The actual builtin row supplies physical arity at the accepted second gate.
Independent Source and native packed rows then recover the original ordered
builtin arguments. The positive payload retains the authentic builtin carrier;
this construction uses no user body law or supplied application packet. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {mapping : LocationMap} {world : StoreTyping}
  {sourceType : TypeSystem.Ty} {sourceValue : Dynamic.Value} {native : Value} {type : Ty}

private theorem function_builtin
    (positive : FunctionOrigins qualification headers keys bodyRegistry faults profile
      mapping world sourceType sourceValue native type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world sourceType sourceValue native type := by
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
  | global member => intro function impossible; cases impossible

private theorem builtin_own_type {function : Dynamic.BuiltinFunction}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      sourceType (.builtin function) native type) :
    CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) native type := by
  cases related with
  | builtin selected number descriptor typed => exact .builtin selected number descriptor typed

/-- Only the retained builtin branch is inverted. Compatible Source views keep
that same compiler builtin, descriptor and ambient capture environment. -/
theorem builtin_member
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType sourceValue native type) :
    ∀ function, sourceValue = .builtin function →
      CallableIndexedBuiltinValues.Represents compiled.indexed world
        function.id.type (.builtin function) native type := by
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

private theorem builtin_native_type {function : Dynamic.BuiltinFunction}
    (related : CallableIndexedBuiltinValues.Represents compiled.indexed world
      function.id.type (.builtin function) native type) :
    type = CallableContract.functionType (SourceCoreInteger.builtinParameter function.id)
      (SourceCoreInteger.builtinResult function.id) := by
  generalize sourceTypeEq : function.id.type = actualSourceType at related
  cases related
  rfl

private theorem builtin_native_count (function : BuiltinFunctionId) :
    (CompatibleBuiltinMeaning.argumentTypes function).length = function.parameterTypes.length := by
  cases function <;> rfl

private theorem values_represents
    {functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {sourceTypes : List TypeSystem.Ty} {nativeTypes : List Ty}
    {arguments : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceTypes nativeTypes arguments payloads) :
    ValuesRep compiled.compatible.checked registry functions mapping world sourceTypes arguments payloads nativeTypes := by
  induction represented with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

section Arguments
variable {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {calleeHeap before : Dynamic.Heap} {store : Store} {canonical : Environment}
  {function : Dynamic.BuiltinFunction} {invocation : Dynamic.EvidenceEnvironment}
  {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {row : SourceCoreStageCodebook.Decision} {unknown : Word}

local notation "positive" => functions qualification headers keys bodyRegistry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry positive

include compiler in
/-- The authentic selected row supplies physical count before the independent
packed type proofs are used to identify the two ordered argument rows. -/
theorem at_arguments
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar site
      callee ids metadata compiler.original function native row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none)
    {arguments : List Dynamic.Value} {payloads : List Value}
    {parameter result sourceResultType : TypeSystem.Ty}
    (calleeRelated : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.builtin function) native compiler.calleeCode.type)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) (.function parameter result))
    (represented : DataExpressionSequence.Values model mapping world
      sourceTypes (compiler.codes.map (·.type)) arguments payloads)
    (sourceBundle : TypeSystem.Ty.productMany sourceTypes = parameter)
    (resultSame : sourceResultType = result) :
    ∃ actualSourceResult,
      SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult ∧
      CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher.Receipt
        (qualification := qualification) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
        (certificates := certificates) (expressionSyntax := expressionSyntax)
        (mapping := mapping) (world := world) (before := before)
        (arguments := arguments) (payloads := payloads)
        positive (.builtin function) invocation native actualSourceResult compiler.resultType := by
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
        (acceptedType.trans (builtin_native_type builtin))
    have physical : function.id.parameterTypes.length = ids.length :=
      builtinAt.parameter_count.symm.trans
        (CallableIndexedOwnedAcceptedIndirectPhysicalArity.selected_count
          builtinAt.selected builtinAt.selected.found accepted)
    have representedCount : compiler.codes.length = arguments.length := by
      simpa only [List.length_map] using represented.length.1
    have actualCount : arguments.length = function.id.parameterTypes.length :=
      representedCount.symm.trans (compiler.ordered_children.1.symm.trans physical.symm)
    have sourceRow : sourceTypes = function.id.parameterTypes :=
      CallableIndexedOwnedStoredArgumentAlignment.source_rows_of_bundle
        ((CallableIndexedOwnedStoredArgumentAlignment.source_length represented).trans actualCount)
        (sourceBundle.trans signature.1)
    have nativePacked : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
        SourceCoreCompatibleCatalog.packTypes (CompatibleBuiltinMeaning.argumentTypes function.id) :=
      (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
        (compiler.packedType.symm.trans
          (nativeSignature.1.trans (CompatibleBuiltinMeaning.argumentTypes_pack function.id).symm))
    have nativeRow : compiler.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function.id :=
      CallableIndexedOwnedStoredArgumentAlignment.native_rows_of_bundle
        (represented.length.1.trans (actualCount.trans (builtin_native_count function.id).symm)) nativePacked
    have exactRows := values_represents represented
    rw [sourceRow, nativeRow] at exactRows
    refine ⟨function.id.returnType, congrArg SourceCoreRawMetadata.runtimeType (resultSame.trans signature.2), ?_⟩
    rw [nativeSignature.2]
    exact .builtin builtin exactRows invocation
  · obtain ⟨inner, impossible, _innerTyped⟩ := staged
    cases impossible

include bridge compiler in
/-- Original Source typing, positive builtin provenance and the genuine second
gate construct the full packet factory at every actual admitted argument post. -/
theorem packets
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeTyped : Dynamic.ValueHasType context calleeHeap (.builtin function) calleeNode.type)
    (represented : PayloadOrigins qualification headers keys bodyRegistry registry faults profile
      mapping world sourceType (.builtin function) native compiler.calleeCode.type)
    (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar site
      callee ids metadata compiler.original function native row)
    (accepted : CallableContract.decision site.gates .beforeApplication unknown row.entry.id = none) :
    CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .builtin function) (calleeNative := native) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge positive compiler := by
  obtain ⟨sourceParameter, sourceResult, calleeType, _typedRows, sourceBundle, resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler parent tree unique parentTyped calleeFound
  rw [calleeType] at calleeTyped
  rcases calleeTyped.builtin_inv with originalType | staged
  · intro middleMap middleWorld middle middleStore arguments payloads types parameter result packed
      argumentState admitted maps worlds _frame _metadata actualTyped _extension rows _heaps _rawArguments _packing _rawBundle
    rcases actualTyped.builtin_inv with actualType | staged
    · have signature := TypeSystem.Ty.function.inj (originalType.trans actualType.symm)
      exact at_arguments compiler (before := middle) actualFunctionType builtinAt accepted
        (represented.extend (SourceCoreRawMetadata.Extends.refl registry) maps worlds) actualTyped rows
        (sourceBundle.trans signature.1) (resultType.trans signature.2)
    · obtain ⟨inner, impossible, _innerTyped⟩ := staged
      cases impossible
  · obtain ⟨inner, impossible, _innerTyped⟩ := staged
    cases impossible

end Arguments
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets
