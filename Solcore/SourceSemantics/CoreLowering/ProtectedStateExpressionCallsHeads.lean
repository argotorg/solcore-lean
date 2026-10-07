import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient

/-! The existing compositional call-head proofs consume one actual protocol
and its certified administrative transport. Every ordered child and call leaf
returns the actual post witness before the next consumer. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedBoundedContracts
universe u v
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {source : TypedSource} {context : SourceSemantics.Context} (evidence : Dynamic.EvidenceEnvironment)
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {reasonAt : ExpressionId → Word}
  (unique : NodeOccurrencesUnique source)
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

namespace WithFacts
variable {Records : Type v} (stateProtocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (post : ExpressionNode → Dynamic.ExpressionOutcome → ∀ {index : ProtectedStateTransition.Index}, stateProtocol.State index → Prop)

/-- This result retains one actual input and one actual post. The post facet is
separate from the runtime relation and all original semantic/effect receipts. -/
def PreservesResult {initialIndex : ProtectedStateTransition.Index}
    (initial : stateProtocol.State initialIndex) (node : ExpressionNode)
    (lowered : SourceCoreBasic.LoweredExpr) (actual : Environment) (ξ : Renaming)
    (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ value finalStore finalMap finalWorld,
    Evaluates actual initialIndex.store (lowered.expression.rename ξ) value finalStore ∧
    GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld node.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends initialIndex.mapping finalMap ∧ WorldExtends initialIndex.world finalWorld ∧
    AdministrativePreserved initialIndex.mapping initialIndex.store finalMap finalStore ∧
    Dynamic.HeapMetadataExtend initialIndex.heap after ∧
    ∃ reached : stateProtocol.State ⟨initialIndex.scope, finalMap, finalWorld, after, finalStore, initialIndex.canonical⟩,
      stateProtocol.Relates initial reached ∧ post node outcome reached

def ReflectsResult {initialIndex : ProtectedStateTransition.Index}
    (initial : stateProtocol.State initialIndex) (node : ExpressionNode)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) (environment : Dynamic.Environment)
    (value : Value) (finalStore : Store) : Prop :=
  ∃ sourceSize outcome after finalMap finalWorld,
    RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment initialIndex.heap id outcome after ∧
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld node.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends initialIndex.mapping finalMap ∧ WorldExtends initialIndex.world finalWorld ∧
    AdministrativePreserved initialIndex.mapping initialIndex.store finalMap finalStore ∧
    Dynamic.HeapMetadataExtend initialIndex.heap after ∧
    ∃ reached : stateProtocol.State ⟨initialIndex.scope, finalMap, finalWorld, after, finalStore, initialIndex.canonical⟩,
      stateProtocol.Relates initial reached ∧ post node outcome reached

variable
  (facts : SourceCoreLocalCell.Scope → ExpressionId → SourceCoreBasic.LoweredExpr → ExpressionNode → Prop)
  (ready : ∀ {index : ProtectedStateTransition.Index}, stateProtocol.State index → Prop)

/-- Only the actual branch certificate is requested. Providers are fixed at
this parent, input and trace, including its authentic static and ready facets. -/
theorem head_preserves_at_with_providers
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store} {canonical actual : Environment}
    {environment : Dynamic.Environment} {ξ : Renaming} {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (initial : stateProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (primitive : CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (data : RecursiveNamedDataExpressionHeadBounds.Certificate calls (.initial compiled.compatible.checked)
      source context reasonAt certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (builtin : BuiltinCalls.Typed.Head (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (tuple : CompatibleExpressionTuples.Certificate (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (call : calls certificate scope id lowered → source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
      PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after)
    (head : CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate scope id lowered)
    (parentFacts : facts scope id lowered node) (initialReady : ready initial)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    PreservesResult (registry := registry) (faults := faults) functions stateProtocol post initial node lowered actual ξ outcome after := by
  cases head with
  | primitive head => exact primitive head found parentFacts initialReady trace
  | constructor receipt form accepted sequence =>
    exact data ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩ found parentFacts initialReady trace
  | member metadata baseMetadata form layout certified =>
    exact data ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩ found parentFacts initialReady trace
  | index header keyFound form sourceType first second =>
    exact data ⟨.index header keyFound form sourceType first second, .index header keyFound form sourceType first second⟩ found parentFacts initialReady trace
  | builtin head => exact builtin head found parentFacts initialReady trace
  | tuple receipt sequence => exact tuple ⟨_, _, _, _, rfl, receipt, sequence⟩ found parentFacts initialReady trace
  | call head => exact call head found parentFacts initialReady trace

/-- The original native parent keeps its exact input and final store. Each
provider returns its independent Source grade at that same actual post. -/
theorem head_reflects_at_with_providers
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {canonical actual : Environment}
    {environment : Dynamic.Environment} {ξ : Renaming} {size : Nat} {value : Value}
    (initial : stateProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (primitive : CompatibleExpressionTypedCompositions.Head compiled.compatible.checked source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (data : RecursiveNamedDataExpressionHeadBounds.Certificate calls (.initial compiled.compatible.checked)
      source context reasonAt certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (builtin : BuiltinCalls.Typed.Head (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (tuple : CompatibleExpressionTuples.Certificate (.initial compiled.compatible.checked) source certificate scope id lowered →
      source.lookupExpression? id = some node → facts scope id lowered node → ready initial → EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (call : calls certificate scope id lowered → source.lookupExpression? id = some node → facts scope id lowered node → ready initial →
      EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
      ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore)
    (head : CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate scope id lowered)
    (parentFacts : facts scope id lowered node) (initialReady : ready initial)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ReflectsResult (program := program) (registry := registry) (faults := faults) (source := source) (context := context) functions evidence stateProtocol post initial node id lowered environment value finalStore := by
  cases head with
  | primitive head => exact primitive head found parentFacts initialReady completed
  | constructor receipt form accepted sequence =>
    exact data ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩ found parentFacts initialReady completed
  | member metadata baseMetadata form layout certified =>
    exact data ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩ found parentFacts initialReady completed
  | index header keyFound form sourceType first second =>
    exact data ⟨.index header keyFound form sourceType first second, .index header keyFound form sourceType first second⟩ found parentFacts initialReady completed
  | builtin head => exact builtin head found parentFacts initialReady completed
  | tuple receipt sequence => exact tuple ⟨_, _, _, _, rfl, receipt, sequence⟩ found parentFacts initialReady completed
  | call head => exact call head found parentFacts initialReady completed
end WithFacts

include extension faithful functionLeaves functionTypes unique missing in
/-- Compositional heads consume the actual ordered child states. -/
theorem head_preserves_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {Records : Type v} (stateProtocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport stateProtocol)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.PreservesAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.PreservesAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.PreservesAt stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial trace
  suffices resolved : WithFacts.PreservesResult  (registry := registry) (faults := faults)
      functions stateProtocol (fun _ _ {_} _ => True) initial node lowered actual ξ outcome after by
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using resolved
  refine WithFacts.head_preserves_at_with_providers (functions := functions) (evidence := evidence)
    (stateProtocol := stateProtocol) (post := fun _ _ {_} _ => True)
    (facts := fun _ _ _ _ => True) (ready := fun {_} _ => True)
    (calls := calls) found initial ?_ ?_ ?_ ?_ ?_ head trivial trivial trace
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedExpressionCompositionsBounds.Stateful.Head.preserves_at functions program evidence
      stateProtocol budget size within unique children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing stateProtocol transport budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedBuiltinHeadBounds.Stateful.Head.preserves_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions functionLeaves program evidence unique
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedTupleHeadBounds.Stateful.preserves_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions program evidence
      stateProtocol budget size within unique children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.PreservesResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (callMeaning branch parentFound environments heaps locals agrees typed initial childTrace)

include extension faithful functionLeaves functionTypes missing in
/-- Reflection uses the same actual child posts at their native grades. -/
theorem head_reflects_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    {Records : Type v} (stateProtocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport stateProtocol)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → ProtectedStateTransition.ReflectsAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults child)
    (callMeaning : ProtectedStateTransition.ReflectsAt
      stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source (calls certificate) faults size) :
    ProtectedStateTransition.ReflectsAt stateProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate) faults size := by
  intro scope id lowered head node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial trace
  suffices resolved : WithFacts.ReflectsResult (program := program) (source := source) (context := context) (registry := registry) (faults := faults)
      functions evidence stateProtocol (fun _ _ {_} _ => True) initial node id lowered environment value finalStore by
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using resolved
  refine WithFacts.head_reflects_at_with_providers (functions := functions) (evidence := evidence)
    (stateProtocol := stateProtocol) (post := fun _ _ {_} _ => True)
    (facts := fun _ _ _ _ => True) (ready := fun {_} _ => True)
    (calls := calls) found initial ?_ ?_ ?_ ?_ ?_ head trivial trivial trace
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedExpressionCompositionsBounds.Stateful.Head.reflects_at functions program evidence
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing stateProtocol transport budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedBuiltinHeadBounds.Stateful.Head.reflects_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions functionLeaves program evidence
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (RecursiveNamedTupleHeadBounds.Stateful.reflects_at (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (registry := registry) (faults := faults) functions program evidence
      stateProtocol budget size within children branch parentFound environments heaps locals agrees typed initial childTrace)
  · intro branch parentFound _facts _ready childTrace
    simpa only [WithFacts.ReflectsResult, ProtectedStateTransition.Transition, SourceCoreCompatibleValues.Context.initial, and_true] using
      (callMeaning branch parentFound environments heaps locals agrees typed initial childTrace)

end Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
