import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionHeadBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer

/-! Constructor, member and index heads consume genuine Source typing at their
actual input. Index's exact successful base post supplies key admission; its
terminal helper retains the same Source heap. The returned full parent trace
establishes post admission at that same reached state. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedDataHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open ProtectedStateExpressionOperandTyping
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : FunctionCalls.FaultRep}
  {calls : CompatibleExpressionCalls.CallHeads} {reasonAt : ExpressionId → Word}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include transport extension faithful functionLeaves functionTypes missing

/-- Genuine parent typing supplies the original operand row independently of
the constructor's generated payload vector and native child types. -/
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate calls values source context reasonAt certificate)
      faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedDataExpressionHeadBounds.Stateful.WithReady.Head.preserves_at functions extension faithful
      functionLeaves functionTypes program evidence unique missing callerProtocol transport
      (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.PreservesAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.preserves_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      (fun {ids types codes} same sequence {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout actualTyped state ready =>
        CallableIndexedOwnedAdmittedSequenceProducer.preserves bridge state ready sequence unique
          (by simpa only [same] using operandTyped) env hp lc layout actualTyped (budget + 1)
          (fun n bound => meaning n (by omega)))
      environments heaps locals agrees typed initial admitted trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- Native reflection keeps its independent whole Source grade and actual
terminal witness before Source preservation supplies success-only admission. -/
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique source) (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source) (covers : evidence.Covers context)
    (meaning : ∀ childSize, childSize ≤ budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source certificate faults childSize) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      context evidence source
      (RecursiveNamedDataExpressionHeadBounds.Certificate calls values source context reasonAt certificate)
      faults size := by
  intro scope id lowered tree node found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial admitted completed
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    RecursiveNamedDataExpressionHeadBounds.Stateful.WithReady.Head.reflects_raw_at functions extension faithful
      functionLeaves functionTypes program evidence missing callerProtocol transport
      (Admission bridge context) budget size bounded tree found
      (fun child member childSize bound => ProtectedStateTransition.WithReady.ReflectsAt.of_sequence callerProtocol
        (Admission bridge context) (CallableIndexedOwnedAdmittedExpressionSequence.reflects_child_at bridge
          unique operandTyped member (meaning childSize bound)))
      (fun {ids types codes} same sequence {mapping world administrative environment canonical actual actualContext before store ξ}
          env hp lc layout actualTyped state ready =>
        CallableIndexedOwnedAdmittedSequenceProducer.reflects bridge state ready sequence unique
          (by simpa only [same] using operandTyped) env hp lc layout actualTyped (budget + 1)
          (fun n bound => meaning n (by omega)))
      environments heaps locals agrees typed initial admitted completed
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sized, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped sized frame⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedDataHeadBounds
