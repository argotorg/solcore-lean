import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeOriginReadReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualInitializedClosureReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureArgumentReceipts

/-! Actual successful callee posts retain a positive static closure member, the genuine
raw Source type and the native compiler type at the same reached state. These
finite projections derive the ordered Source and native aggregate equalities
needed by receiving-model stored calls. Physical binder arity and stage gates
remain independent receipts. The body registry stays distinct from outer
payload metadata; no hidden Code equality or registry rebasing is inferred. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallTypeReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualTypedClosureReceipts (StaticMember)
open CallableIndexedOwnedContextualCellOrigins
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)
open CallableIndexedOwnedStoredNativePackReceipts
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {native : Core.Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Core.Ty}

/-- The original contextual producer retains each canonical binder projection,
for ordinary and principal members alike. Only the positive member is used. -/
theorem member_projected_bindings
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore) :
    ∀ binding ∈ bindings,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 :=
  member.projected_bindings

/-- Original Tree indices retain both physical ordered vector lengths. Packed
type equality is not used to recover either length or binder arity. -/
theorem tree_counts {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes) :
    ids.length = types.length ∧ ids.length = codes.length := by
  induction tree with
  | nil => exact ⟨rfl, rfl⟩
  | single _ _ => exact ⟨rfl, rfl⟩
  | cons _ _ _ ih => exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

section Call
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word}
  {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {sourceTypes : List TypeSystem.Ty} {heap : Dynamic.Heap} {calleeNode : ExpressionNode}

/-- Genuine raw closure typing aligns the original parent argument row with
this member's Source binders. The parent's actual empty output path fixes the
raw result type. No native signature or descriptor determines a Source type. -/
theorem source_aggregates
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeTyped : Dynamic.ValueHasType context heap (.closure function) calleeNode.type)
    (member : StaticMember headers keys bodyRegistry faults mapping world
      function native bindings parameterCore resultCore) :
    ExpressionsHaveTypes source context ids sourceTypes ∧
    TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) ∧
    compiler.original.type = function.resultType := by
  generalize reportedEq : compiler.original.type = reported at parentTyped
  cases parentTyped with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans compiler.found)
    subst actualNode
    rw [compiler.originalForm] at raw
    cases raw with
    | indirectCall calleeTyping argumentsTyping application =>
      have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
        unique calleeFound calleeTyping
      rw [reported] at calleeTyped
      have closure := Dynamic.ValueHasType.closure_function_inv calleeTyped
      have row := CallableIndexedOwnedContextualInitializedClosureReceipts.source_types_at_tree
        unique tree argumentsTyping
      have bundle := CallableIndexedOwnedStoredClosureArgumentReceipts.empty_bundle
        application compiler.argumentCoercions
      have sourceBundle : TypeSystem.Ty.productMany sourceTypes =
          TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body)) := by
        rw [← row]
        exact bundle.trans (closure.1.trans (congrArg TypeSystem.Ty.productMany member.source_binders.symm))
      have result := requirements.outputPath.foldl_target
      rw [parent.coercions, List.foldl_nil] at result
      exact ⟨row ▸ argumentsTyping, sourceBundle, result.symm.trans closure.2.1⟩

/-- Actual native typing aligns the compiler's two types with the retained
member. Only runtime typing is needed here, so body and payload registries
are not identified to invoke a one-registry representation helper. -/
theorem native_parameters
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore)
    (typed : RuntimeValueHasType world native compiler.calleeCode.type compiled.indexed.layouts.definitions) :
    compiler.parameterType = parameterCore ∧ compiler.resultType = resultCore := by
  have accepted := compiler.callableType
  rw [actualFunctionType] at accepted
  have selected := member.native_type
  exact callable_parameters (accepted.trans (typed.type_eq.symm.trans selected))

/-- The positive member and all aggregates belong to the original caller's
actual compiler vector. This receipt deliberately carries no stage verdict or
binder-count equality, which need separate genuine acceptance facts. -/
structure TypedCallAt : Prop where
  member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore
  arguments : ExpressionsHaveTypes source context ids sourceTypes
  sourceCount : ids.length = sourceTypes.length
  compilerCount : ids.length = compiler.codes.length
  sourceBundle : TypeSystem.Ty.productMany sourceTypes =
    TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))
  nativeBundle : SourceCoreCompatibleCatalog.packTypes (compiler.codes.map (·.type)) =
    SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd)
  rawResult : compiler.original.type = function.resultType
  nativeParameter : compiler.parameterType = parameterCore
  nativeResult : compiler.resultType = resultCore
  rawCalleeView : SourceCoreRawMetadata.runtimeType calleeNode.type =
    SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType function)

/-- Positive classification projects the real static member and its syntax/owner;
actual raw typing and native typing then derive the required aggregate facts.
The original callee node is supplied by its real Source lookup. -/
theorem at_typed_callee
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (calleeTyped : Dynamic.ValueHasType context heap (.closure function) calleeNode.type)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (payload : PayloadOrigins headers keys bodyRegistry registry faults profile mapping world
      calleeNode.type (.closure function) native compiler.calleeCode.type) :
    ∃ bindings parameterCore resultCore,
      TypedCallAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults)
        (mapping := mapping) (world := world) (function := function) (native := native)
        (bindings := bindings) (parameterCore := parameterCore) (resultCore := resultCore)
        (context := context) (sourceTypes := sourceTypes) (calleeNode := calleeNode) compiler := by
  obtain ⟨bindings, parameterCore, resultCore, member, _nativeView, rawView⟩ :=
    (CallableIndexedOwnedContextualCalleeOriginReadReceipts.callable_at profile payload
      (.closure function)).closure_member
  obtain ⟨arguments, sourceBundle, rawResult⟩ :=
    source_aggregates compiler parent tree unique parentTyped calleeFound calleeTyped member
  have nativeTypes := native_parameters compiler actualFunctionType member payload.runtime_hasType
  have bindingPack := member.parameter_core profile
  have nativeBundle := (CompatibleExpressionConstructorNativeTyping.packed_type compiler.codes).symm.trans
    (compiler.packedType.symm.trans (nativeTypes.1.trans bindingPack))
  have counts := tree_counts tree
  exact ⟨bindings, parameterCore, resultCore,
    member, arguments, counts.1, counts.2, sourceBundle, nativeBundle, rawResult,
    nativeTypes.1, nativeTypes.2, rawView⟩

/-- The genuine successful child post supplies raw closure typing and positive
payload at its exact reached state. Admission and cells remain at that same
witness; this static adapter performs no callee evaluation or invocation. -/
theorem at_callee_post
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0}
      (CallableIndexedOwnedFunctionState.Records keys)}
    (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    {index : ProtectedStateTransition.Index}
    (reached : callerProtocol.State index)
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (unique : NodeOccurrencesUnique source)
    (parentTyped : ExpressionHasType source context id compiler.original.type)
    (calleeFound : source.lookupExpression? callee = some calleeNode)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
    (post : PostWithOrigins (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      bridge context profile calleeNode.type compiler.calleeCode.type
      (.value (.closure function)) (.inRight .word native) reached) :
    ∃ bindings parameterCore resultCore,
      TypedCallAt (headers := headers) (keys := keys) (bodyRegistry := bodyRegistry) (faults := faults)
        (mapping := index.mapping) (world := index.world) (function := function) (native := native)
        (bindings := bindings) (parameterCore := parameterCore) (resultCore := resultCore)
        (context := context) (sourceTypes := sourceTypes) (calleeNode := calleeNode) compiler ∧
      CallableIndexedOwnedSourceAdmission.Admission bridge context reached ∧
      CellOrigins headers keys bodyRegistry registry faults profile
        index.mapping index.world index.heap index.store := by
  have successful := post.at_value
  obtain ⟨bindings, parameterCore, resultCore, typed⟩ :=
    at_typed_callee compiler parent tree unique parentTyped calleeFound successful.2.1 profile
      actualFunctionType successful.2.2
  exact ⟨bindings, parameterCore, resultCore, typed, successful.1, post.cells⟩

end Call
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualStoredCallTypeReceipts
