import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyOrigins

/-! Pointwise contracts at one complete actual body entry. They keep every
original semantic field and the actual reached state, without quantifying over
unrelated canonical captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
universe u v
variable {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u, v} Records}
  {conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop}
  (functions : FunctionModel values.checked.catalog ambient) (program : Program)
  {origin : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults}

/-- Source meaning at the complete actual parameter entry. -/
def PreservesAt (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions)
    (size : Nat) : Prop :=
  ∀ {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    RecursiveNamedCallBounds.BodyTrace program size origin.function origin.context entry.environment entry.heap outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates entry.actual entry.store (origin.code.rename entry.embedding) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- Original native completion at that same actual parameter entry. -/
def ReflectsAt (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions)
    (size : Nat) : Prop :=
  ∀ {value : Value} {finalStore : Store},
    EvaluationSize size entry.actual entry.store (origin.code.rename entry.embedding) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize origin.function origin.context entry.environment entry.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld origin.function.resultType origin.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends entry.mapping finalMap ∧ WorldExtends entry.world finalWorld ∧
      AdministrativePreserved entry.mapping entry.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend entry.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld origin.administrative program
        origin.function origin.context origin.scope entry.environment entry.heap after outcome ∧
      ProtectedStateTransition.Transition protocol entry.initial
        ⟨origin.scope, finalMap, finalWorld, after, finalStore, entry.canonical⟩

/-- The retained uniform body contract specializes to the actual entry. -/
theorem preserves_of_uniform {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.PreservesAt protocol conditionGate functions program origin size)
    (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions) :
    PreservesAt functions program entry size := meaning entry

/-- Native specialization keeps the independently reconstructed Source grade. -/
theorem reflects_of_uniform {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.ReflectsAt protocol conditionGate functions program origin size)
    (entry : CallableRuntimeBodyOrigins.Stateful.Entry protocol conditionGate origin functions) :
    ReflectsAt functions program entry size := meaning entry

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
