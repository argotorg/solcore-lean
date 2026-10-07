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
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Stateful.Head.preserves_at functions program evidence
      stateProtocol budget size within unique children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing stateProtocol
      transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing stateProtocol
      transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence unique missing stateProtocol
      transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Stateful.Head.preserves_at functions functionLeaves program evidence unique
      stateProtocol budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.Stateful.preserves_at functions program evidence
      stateProtocol budget size within unique children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

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
  intro scope id lowered head
  cases head with
  | primitive head =>
    exact RecursiveNamedExpressionCompositionsBounds.Stateful.Head.reflects_at functions program evidence
      stateProtocol budget size within children head
  | constructor receipt form accepted sequence =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing stateProtocol
      transport budget size within children
      ⟨.constructor receipt form accepted sequence, .constructor receipt form accepted sequence⟩
  | member metadata baseMetadata form layout certified =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing stateProtocol
      transport budget size within children
      ⟨.member metadata baseMetadata form layout certified, .member metadata baseMetadata form layout certified⟩
  | index header found form sourceType first second =>
    exact RecursiveNamedDataExpressionHeadBounds.Stateful.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (context := context) (source := source) (certificate := certificate) functions extension faithful functionLeaves functionTypes
      program evidence missing stateProtocol
      transport budget size within children
      ⟨.index header found form sourceType first second, .index header found form sourceType first second⟩
  | builtin head =>
    exact RecursiveNamedBuiltinHeadBounds.Stateful.Head.reflects_at functions functionLeaves program evidence
      stateProtocol budget size within children head
  | tuple receipt sequence =>
    exact RecursiveNamedTupleHeadBounds.Stateful.reflects_at functions program evidence
      stateProtocol budget size within children
      ⟨_, _, _, _, rfl, receipt, sequence⟩
  | call head => exact callMeaning head

end Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
