import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins
import Solcore.SourceSemantics.CoreLowering.ProtectedStateFunctionFinishReady

/-! Readiness and genuine body facts accompany the original actual entry.
The static origin, protected state, environment and physical reads are retained
verbatim. Source and native contracts expose the same reached finish state and
keep their independent grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyOrigins
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableRuntimeBodyOrigins
open RecursiveNamedLexicalContracts.Stateful.WithReady (Readiness)
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)

structure Entry (origin : StaticOrigin values ambient registry faults)
    (functions : FunctionModel values.checked.catalog ambient) where
  original : Stateful.Entry protocol conditionGate origin functions
  bodyFacts : facts origin.context true origin.function.body origin.function.resultType
  ready : readiness.Ready origin.context original.initial

variable (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  (origin : StaticOrigin values ambient registry faults)

def PreservesAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol readiness conditionGate facts origin functions)
      {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context
      entry.original.environment entry.original.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.original.actual entry.original.store (origin.code.rename entry.original.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.original.mapping finalMap ∧ WorldExtends entry.original.world finalWorld ∧
      AdministrativePreserved entry.original.mapping entry.original.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.original.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.original.environment entry.original.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness origin.context outcome entry.original.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.original.canonical⟩

def ReflectsAt (size : Nat) : Prop :=
  ∀ (entry : Entry protocol readiness conditionGate facts origin functions)
      {value : Value} {finalStore : Store},
    EvaluationSize size entry.original.actual entry.original.store
      (origin.code.rename entry.original.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context
        entry.original.environment entry.original.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.original.mapping finalMap ∧ WorldExtends entry.original.world finalWorld ∧
      AdministrativePreserved entry.original.mapping entry.original.store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend entry.original.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.original.environment entry.original.heap after outcome ∧
      ProtectedStateTransition.FunctionFinish.Reached readiness origin.context outcome entry.original.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.original.canonical⟩

section Trivial
variable {protocol conditionGate functions program origin} {size : Nat}

theorem PreservesAt.of_trivial
    (meaning : Stateful.PreservesAt protocol conditionGate functions program origin size) :
    PreservesAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size := by
  intro entry outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ := meaning entry.original trace
  obtain ⟨last, related⟩ := reached
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, last, related, by cases outcome <;> exact True.intro⟩

theorem PreservesAt.forget_trivial
    (meaning : PreservesAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size) :
    Stateful.PreservesAt protocol conditionGate functions program origin size := by
  intro entry outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ :=
    meaning ⟨entry, True.intro, True.intro⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached.forget⟩

theorem ReflectsAt.of_trivial
    (meaning : Stateful.ReflectsAt protocol conditionGate functions program origin size) :
    ReflectsAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size := by
  intro entry value finalStore evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ := meaning entry.original evaluated
  obtain ⟨last, related⟩ := reached
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, last, related, by cases outcome <;> exact True.intro⟩

theorem ReflectsAt.forget_trivial
    (meaning : ReflectsAt protocol (Readiness.trivial protocol) conditionGate (fun _ _ _ _ => True)
      functions program origin size) :
    Stateful.ReflectsAt protocol conditionGate functions program origin size := by
  intro entry value finalStore evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached⟩ :=
    meaning ⟨entry, True.intro, True.intro⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps,
    maps, worlds, preserved, metadata, lexical, reached.forget⟩

end Trivial
end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyReadyOrigins
