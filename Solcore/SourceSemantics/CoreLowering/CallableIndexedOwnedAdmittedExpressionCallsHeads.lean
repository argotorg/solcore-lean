import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionCallsHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedCompositionsBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedDataHeadBounds

/-! Genuine parent Source typing and actual input admission select the existing
head producers. Each branch returns its own actual reached witness and post
admission. Calls retain an explicit producer for their authentic certificate;
this dispatcher adds no body-family closure or execution induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
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
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)

include transport extension faithful functionLeaves functionTypes unique missing wellFormed runtime covers

theorem preserves_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults child)
    (callMeaning : CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (calls certificate) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate)
      faults size := by
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  change ProtectedStateExpressionCallsHeads.WithFacts.PreservesResult
    (registry := registry) (faults := faults) functions callerProtocol
    (fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached) initial node lowered actual ξ outcome after
  refine ProtectedStateExpressionCallsHeads.WithFacts.head_preserves_at_with_providers
    (functions := functions) (evidence := evidence) (stateProtocol := callerProtocol)
    (post := fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached)
    (facts := fun _ id _ node => ExpressionHasType source context id node.type)
    (ready := Admission bridge context) (calls := calls)
    found initial ?_ ?_ ?_ ?_ ?_ head sourceTyped admitted trace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedCompositionsBounds.preserves_at bridge functions budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedDataHeadBounds.preserves_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge transport functions extension faithful functionLeaves functionTypes missing budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Builtin.preserves_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique functionLeaves budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Tuple.preserves_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact callMeaning branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace

theorem reflects_at_with_calls
    (calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate)
    (budget size : Nat) (within : size ≤ budget)
    (children : ∀ child, child ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source certificate faults child)
    (callMeaning : CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source (calls certificate) faults size) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      context evidence source
      (CompatibleExpressionCalls.Head calls (.initial compiled.compatible.checked) source context reasonAt certificate)
      faults size := by
  intro scope id lowered head node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted trace
  change ProtectedStateExpressionCallsHeads.WithFacts.ReflectsResult (program := program) (source := source) (context := context)
    (registry := registry) (faults := faults) functions evidence callerProtocol
    (fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached) initial node id lowered environment value finalStore
  refine ProtectedStateExpressionCallsHeads.WithFacts.head_reflects_at_with_providers
    (functions := functions) (evidence := evidence) (stateProtocol := callerProtocol)
    (post := fun node outcome {_} reached => PostAdmission bridge context node.type outcome reached)
    (facts := fun _ id _ node => ExpressionHasType source context id node.type)
    (ready := Admission bridge context) (calls := calls)
    found initial ?_ ?_ ?_ ?_ ?_ head sourceTyped admitted trace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedCompositionsBounds.reflects_at bridge functions budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedDataHeadBounds.reflects_at (calls := calls)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge transport functions extension faithful functionLeaves functionTypes missing budget size within
      unique wellFormed runtime covers children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Builtin.reflects_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique functionLeaves budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact CallableIndexedOwnedAdmittedSequenceHeads.Tuple.reflects_at
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      bridge functions evidence wellFormed runtime covers unique budget size within children branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace
  · intro branch parentFound parentTyped actualAdmission childTrace
    exact callMeaning branch parentFound parentTyped environments heaps locals agrees typed initial actualAdmission childTrace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionCallsHeads
