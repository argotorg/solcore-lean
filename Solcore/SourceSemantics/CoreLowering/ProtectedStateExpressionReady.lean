import Solcore.SourceSemantics.CoreLowering.ProtectedStateSequenceBridge

/-! Readiness accompanies the same concrete expression state and is required
only after success. Source and native grades remain independent. These bridges
reuse the existing ordered sequence contracts and add no execution fold. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (ready : ∀ {index : Index}, protocol.State index → Prop)

def Reached (outcome : Dynamic.ExpressionOutcome) {initial : Index}
    (state : protocol.State initial) (final : Index) : Prop :=
  ∃ reached : protocol.State final,
    protocol.Relates state reached ∧ ∀ value, outcome = .value value → ready reached

theorem Reached.of_value {initial final : Index} {state : protocol.State initial}
    {value : Dynamic.Value} (transition : Reached protocol ready (.value value) state final)
    (outcome : Dynamic.ExpressionOutcome) : Reached protocol ready outcome state final := by
  obtain ⟨reached, related, successful⟩ := transition
  exact ⟨reached, related, fun _ _ => successful _ rfl⟩

theorem Reached.continue {initial middle final : Index}
    {state : protocol.State initial} {middleState : protocol.State middle}
    {outcome : Dynamic.ExpressionOutcome} (first : protocol.Relates state middleState)
    (second : Reached protocol ready outcome middleState final) :
    Reached protocol ready outcome state final := by
  obtain ⟨reached, related, successful⟩ := second
  exact ⟨reached, protocol.trans first related, successful⟩

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
    ready initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

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
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

end Expressions

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {size : Nat}

theorem PreservesAt.to_sequence
    (meaning : PreservesAt protocol ready model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt protocol ready size model
      program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial initialReady trace
  exact meaning certified found environments heaps locals agrees typed initial initialReady (SequenceBridge.call_trace trace)

theorem ReflectsAt.to_sequence
    (meaning : ReflectsAt protocol ready model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt protocol ready size model
      program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, SequenceBridge.source_trace trace, rest⟩

theorem PreservesAt.of_sequence
    (meaning : ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt protocol ready size model
      program context evidence source certificate faults) :
    PreservesAt protocol ready model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial initialReady trace
  exact meaning certified found environments heaps locals agrees typed initial initialReady (SequenceBridge.source_trace trace)

theorem ReflectsAt.of_sequence
    (meaning : ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt protocol ready size model
      program context evidence source certificate faults) :
    ReflectsAt protocol ready model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, SequenceBridge.call_trace trace, rest⟩

theorem PreservesAt.of_stateful
    (meaning : ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate faults size) :
    PreservesAt protocol (fun _ => True) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial _ trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related⟩ := meaning certified found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, fun _ _ => True.intro⟩

theorem ReflectsAt.of_stateful
    (meaning : ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate faults size) :
    ReflectsAt protocol (fun _ => True) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial _ evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related⟩ := meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, fun _ _ => True.intro⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.WithReady
