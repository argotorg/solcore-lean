import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectParentPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues

/-! The exact prepared model is observed at the one actual successful callee
post. Its prior branch remains a genuine General selection alternative. A
closure identity and attached Dispatch/Selected inputs are consumed only at
that post; no classifier existence or prepared origin for prior values is
asserted. The original ordered child proofs run once in the common core. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler native)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

local notation "functions" => CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (sidecarSource : sidecar.source = source)

variable {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source) (parent : SourceParent compiler)

/-- Exact selection and the original conditional resolver share this same
actual post. The selected value may retain the unresolved prior branch. -/
def ValuePrefix (budget : Nat) (value : Value) (finalStore : Store) : Prop :=
  ∃ nativeSize sourceSize sourceValue after carrier calleeStore finalMap finalWorld,
    EvaluationSize nativeSize actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore ∧ nativeSize < budget ∧
    SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before callee sourceValue after ∧
    CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
      (actual := actual) (ξ := ξ) (calleeNode := calleeNode) (context := context)
      bridge functions compiler initial sourceValue after carrier calleeStore finalMap finalWorld ∧
    CallableIndexedOwnedStoredIndirectNativePrefix.GatePrefix budget prepared.site native.diagnostics.unknown compiler.resultType
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ) actual calleeStore carrier value finalStore ∧
    ∀ (function : Dynamic.Closure), sourceValue = .closure function →
      CallableIndexedOwnedPreparedOrdinaryLambdaValues.Selected
        (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        (mapping := finalMap) (world := finalWorld) (raw := calleeNode.type)
        (function := function) (native := carrier) (type := compiler.calleeCode.type) ∧
      ∀ (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
          (.closure function) carrier)
        (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata
          compiler.original dispatch.row),
        CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.ClosureResolutionWithEffects
          (registry := registry) (faults := faults) (context := context) (evidence := evidence)
          (calleeNode := calleeNode) (environment := environment) (actual := actual) (ξ := ξ)
          (calleeMap := finalMap) (calleeWorld := finalWorld) (calleeHeap := after)
          (calleeStore := calleeStore) (calleeSize := sourceSize) (sourceTypes := sourceTypes)
          bridge functions compiler prepared initial dispatch budget value finalStore

include prepared certified found sourceTyped parentTyped wellFormed runtime covers
  environments heaps locals agrees typed admitted caller sidecarSource tree unique parent in
/-- Strict children of the same family construct the actual callee post.
Exact model inversion observes that post before any conditional closure resolver. -/
theorem reflects_parent (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar ∧
    sidecar.source = source ∧
    (CallableIndexedOwnedStoredIndirectNativePrefix.ForModel.FaultPrefix
        (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (sidecar := sidecar)
        bridge functions compiler initial budget value finalStore ∨
      ValuePrefix (registry := registry) (faults := faults) (context := context) (evidence := evidence)
        (environment := environment) (actual := actual) (ξ := ξ) (calleeNode := calleeNode)
        (sourceTypes := sourceTypes) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) := by
  obtain ⟨sameCaller, sameSource, produced⟩ :=
    CallableIndexedOwnedStoredIndirectParentPrefix.ForModel.reflects_parent_with_effects
      bridge functions compiler prepared certified found sourceTyped parentTyped wellFormed runtime covers
      environments heaps locals agrees typed initial admitted caller sidecarSource tree unique parent
      budget children completed within
  refine ⟨sameCaller, sameSource, ?_⟩
  rcases produced with failed | succeeded
  · exact Or.inl failed
  · right
    obtain ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, resolver⟩ := succeeded
    refine ⟨nativeSize, sourceSize, sourceValue, after, carrier, calleeStore, finalMap, finalWorld,
      child, childStrict, trace, post, gate, ?_⟩
    intro function sameClosure
    have exactValue : ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        calleeNode.type (.closure function) carrier compiler.calleeCode.type := sameClosure ▸ post.2.1
    exact ⟨CallableIndexedOwnedPreparedOrdinaryLambdaValues.selected_of_value profile exactValue,
      resolver function sameClosure⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStoredIndirectParentPrefix
