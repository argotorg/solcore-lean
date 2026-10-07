import Solcore.SourceSemantics.CoreLowering.ProtectedState
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts

/-! Sized expression contracts return the actual reached protected state.
Compatibility adapters retain existing execution and heap results. Ordinary
administrative adapters preserve the complete record observation; dynamic
record production requires a separately proved transition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)

theorem AdministrativeTransport.toProtectedTransport (transport : AdministrativeTransport protocol) :
    ProtectedExpressionMeaning.Transport (entry protocol) where
  extend := by
    intro scope mapping world before store canonical futureMap futureWorld after futureStore
      installed maps worlds frame metadata
    obtain ⟨state⟩ := installed
    exact ⟨transport.extend state maps worlds frame metadata⟩

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
  (faults : GenericExpressionMeaning.FaultRep)

def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

theorem PreservesAt.forget {size : Nat}
    (meaning : PreservesAt protocol model program context evidence source certificate faults size) :
    RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults (entry protocol) := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed installed trace
  obtain ⟨initial⟩ := installed
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    meaning certified found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem ReflectsAt.forget {size : Nat}
    (meaning : ReflectsAt protocol model program context evidence source certificate faults size) :
    RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults (entry protocol) := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed installed evaluated
  obtain ⟨initial⟩ := installed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- A proved legacy contract can extend its input witness through its certified
administrative effects. Its post-witness has the same record observation. -/
theorem PreservesAt.of_administrative (transport : AdministrativeTransport protocol) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults (entry protocol)) :
    PreservesAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition protocol transport initial maps worlds frame metadata⟩

theorem ReflectsAt.of_administrative (transport : AdministrativeTransport protocol) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults (entry protocol)) :
    ReflectsAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition protocol transport initial maps worlds frame metadata⟩

end Expressions

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
