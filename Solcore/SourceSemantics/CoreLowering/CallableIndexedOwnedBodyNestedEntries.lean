import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCanonicalState

/-! A genuine nested formation packet accompanies one complete actual body
entry. The wrapper preserves the same underlying input and reached pools. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyNestedEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (principal : CallableIndexedOwnedFunctionValues.Header compiled program)
  {conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  (entry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys) conditionGate origin functions)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner principal _ entry.initial)

def wrap : CallableRuntimeBodyOrigins.Stateful.Entry
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal) conditionGate origin functions :=
  { entry with initial := ⟨entry.initial, packet⟩ }

theorem preserves_of_nested {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner principal entry packet) size) :
    CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

theorem reflects_of_nested {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner principal)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner principal entry packet) size) :
    CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyNestedEntries
