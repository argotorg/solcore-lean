import Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
import Solcore.SourceSemantics.CoreLowering.CoreEvaluationSize
import Solcore.SourceSemantics.CoreLowering.ProtectedState
import Solcore.SourceSemantics.CoreLowering.ExpressionFailurePostContracts

/-! Actual ready children retain a fault post at the same returned tuple.
These contracts supply no execution or chosen primitive witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedReadyExpressionFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open ProtectedStateTransition
open GenericExpressionMeaning (Certificate FaultRep)
universe u v

abbrev SourceTrace := Program → Nat → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → ExpressionId → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop

def ExpressionPreservesAt (traceAt : SourceTrace) {Records : Type v} (protocol : Protocol.{u, v} Records) (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop) (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    traceAt program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sourceValue, outcome = .value sourceValue → ready reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore

def ExpressionReflectsAt (traceAt : SourceTrace) {Records : Type v} (protocol : Protocol.{u, v} Records) (ready : ∀ {index : ProtectedStateTransition.Index}, protocol.State index → Prop) (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (certificate : Certificate) (faults : FaultRep) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      traceAt program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ∀ sourceValue, outcome = .value sourceValue → ready reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore

end Solcore.SourceSemantics.CoreLowering.ProtectedReadyExpressionFaultPostContracts
