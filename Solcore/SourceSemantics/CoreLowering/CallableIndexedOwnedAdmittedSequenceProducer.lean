import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionSequence

/-! Genuine Source typing and actual input admission instantiate a neutral
whole-sequence producer. Only the extra post-admission proof is forgotten;
the full result, effects and identical reached witness remain. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes originalSourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes codes)
  (unique : NodeOccurrencesUnique source)
  (typing : ExpressionsHaveTypes source context ids originalSourceTypes)
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)

include admitted tree unique typing environments heaps locals agrees typed in
/-- Source uses the original inclusive sequence budget at this actual input. -/
theorem preserves (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
      model context evidence source certificate faults size) :
    ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := sourceTypes)
      (codes := codes) (faults := faults) model initial budget := by
  intro size outcome after execution bounded
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.preserves_bounded bridge budget tree unique typing meaning
      environments heaps locals agrees typed initial admitted execution bounded
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩

include admitted tree unique typing environments heaps locals agrees typed in
/-- Native keeps its strict budget and independently graded Source trace. -/
theorem reflects (budget : Nat)
    (meaning : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
      model context evidence source certificate faults size) :
    ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) (sourceTypes := sourceTypes)
      (codes := codes) (faults := faults) model initial budget := by
  intro size value finalStore completed bounded
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, _post⟩ :=
    CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique typing meaning
      environments heaps locals agrees typed initial admitted completed bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedSequenceProducer
