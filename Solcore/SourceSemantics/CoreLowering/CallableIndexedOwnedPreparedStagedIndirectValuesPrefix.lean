import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds

/-! Source preservation constructs the callee and ordered argument prefix
at their actual reached states. It retains callee typing and its complete
post for builtin and user application. The application itself follows later. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectValuesPrefix
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {calleeNode : ExpressionNode}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (view : CallableIndexedOwnedContextualDiagnosticSources.SourceView sidecar.source source)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions


/-- Both native prefix actions use the same represented callee and argument
packet. The callee post is retained before the argument effects are composed. -/
def ValuesPrefix (sourceValue : Dynamic.Value) (calleeHeap argumentsHeap : Dynamic.Heap)
    (sources : List Dynamic.Value) : Prop :=
  ∃ rawParameter rawResult,
    calleeNode.type = .function rawParameter rawResult ∧
    TypeSystem.Ty.productMany sourceTypes = rawParameter ∧ compiler.original.type = rawResult ∧
  ∃ calleeStore calleeMap calleeWorld carrier values argumentsStore finalMap finalWorld
      originalNode originalMetadata,
    CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
      (calleeNode := calleeNode) bridge functions compiler initial
      sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld ∧
    Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type ∧
    Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore ∧
    Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore ∧
    DataExpressionSequence.Values model finalMap finalWorld sourceTypes
      (compiler.codes.map (·.type)) sources values ∧
    GenericHeap.PayloadModel.Represents model finalMap finalWorld calleeNode.type
      sourceValue carrier compiler.calleeCode.type ∧
    CallView originalNode compiler.original originalMetadata metadata ∧
    BoundaryAt sidecar prepared.site callee ids originalMetadata originalNode sourceValue carrier ∧
    GenericHeap.HeapRepresents model finalMap finalWorld argumentsHeap argumentsStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap argumentsStore ∧ Dynamic.HeapMetadataExtend before argumentsHeap ∧
    ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, argumentsHeap, argumentsStore, canonical⟩,
      callerProtocol.Relates initial reached ∧ Admission bridge context reached

include prepared sourceEq certified found sourceTyped environments heaps locals agrees typed admitted
  caller view originalUnique guardFrame sourceParent tree unique parentTyped in
/-- Strict callee preservation and the real ordered argument fold construct
the full prefix once. The returned admission belongs to the argument endpoint. -/
theorem preserves_values (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate faults budget)
    {calleeSize argumentsSize : Nat} {sourceValue : Dynamic.Value}
    {calleeHeap argumentsHeap : Dynamic.Heap} {sources : List Dynamic.Value}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (within : Staging.Recursive.Size.stepSize [calleeSize, argumentsSize] ≤ budget) :
    ValuesPrefix (registry := registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ)
      (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources := by
  have calleeStrict : calleeSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := calleeSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have argumentsStrict : argumentsSize < budget := Nat.lt_of_lt_of_le
    (Staging.Recursive.Size.child_lt_stepSize (child := argumentsSize)
      (children := [calleeSize, argumentsSize]) (by simp)) within
  have actualFound : invocation.source.lookupExpression? callee = some calleeNode := by rw [sourceEq]; exact found
  have actualTyped : ExpressionHasType invocation.source context callee calleeNode.type := by rw [sourceEq]; exact sourceTyped
  obtain ⟨value, calleeStore, calleeMap, calleeWorld, calleeEvaluated, representation, calleeHeaps,
    calleeMaps, calleeWorlds, calleeFrame, calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩ :=
    children calleeSize calleeStrict certified actualFound actualTyped environments heaps locals agrees typed initial admitted calleeTrace
  cases representation with
  | value payload =>
      rename_i carrier
      have post : CalleePost (registry := registry) (context := context) (actual := actual) (ξ := ξ)
          (calleeNode := calleeNode) bridge functions compiler initial
          sourceValue calleeHeap carrier calleeStore calleeMap calleeWorld :=
        ⟨calleeEvaluated, payload, calleeHeaps, calleeMaps, calleeWorlds, calleeFrame,
          calleeMetadata, calleeState, calleeRelated, calleeAdmission⟩
      have sourceValueTyped : Dynamic.ValueHasType context calleeHeap sourceValue calleeNode.type :=
        calleeAdmission.at_value.1
      obtain ⟨originalNode, originalMetadata, _contains, _form, callView, boundary⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.scoped_boundary
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped)
          bridge profile compiler prepared initial caller view originalUnique post
      obtain ⟨rawParameter, rawResult, functionType, argumentsTyped, bundle, resultType⟩ :=
        CallableIndexedOwnedPreparedStagedIndirectArgumentPrefix.source_rows
          (sourceEq := sourceEq) (found := found) (sourceParent := sourceParent)
          (tree := tree) (unique := unique) (parentTyped := parentTyped) compiler
      have argumentLayout : EnvironmentsAgree
          (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
          canonical (.unit :: carrier :: actual) := agree_prefix (agree_prefix agrees carrier) Value.unit
      have argumentTyped := RuntimeEnvironmentHasTypes.cons (RuntimeValueHasType.unit (world := calleeWorld))
        (RuntimeEnvironmentHasTypes.cons (GenericHeap.PayloadModel.runtime_hasType model payload) (typed.weaken calleeWorlds))
      obtain ⟨values, argumentsStore, finalMap, finalWorld, argumentsEvaluated, represented, finalHeaps,
        maps, worlds, frame, heapMetadata, reached, related, postAdmission⟩ :=
        CallableIndexedOwnedAdmittedStagedExpressionSequence.preserves_values bridge budget tree unique argumentsTyped children
          (environments.extend calleeMaps calleeWorlds) calleeHeaps (locals.mono calleeMetadata) argumentLayout
          argumentTyped calleeState calleeAdmission.at_value.2 argumentsTrace (Nat.le_of_lt argumentsStrict)
      have gate := CallableIndexedOwnedPreparedStagedIndirectArgumentFaultBounds.first_gate
        (actual := actual) compiler prepared guardFrame boundary accepted calleeStore
      exact ⟨rawParameter, rawResult, functionType, bundle, resultType, calleeStore, calleeMap, calleeWorld,
        carrier, values, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata,
        post, sourceValueTyped, gate, argumentsEvaluated, represented,
        GenericHeap.PayloadModel.extend model payload maps worlds, callView, boundary, finalHeaps,
        calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame,
        calleeMetadata.trans heapMetadata, reached, callerProtocol.trans calleeRelated related,
        postAdmission.at_values⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectValuesPrefix
