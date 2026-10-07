import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyEntryContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState

/-! An authentic canonical-slot packet wraps one complete actual body entry.
Only that proof is forgotten at the returned pool; every original semantic
field and the exact actual initial/post witnesses remain intact. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
  {conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop}
  {origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults}
  (entry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys) conditionGate origin functions)
  (globals : Globals (headers := headers) owner callerPrefix origin.scope entry.canonical)

/-- The same original entry, with genuine canonical slots beside its actual pool. -/
def wrap : CallableRuntimeBodyOrigins.Stateful.Entry
    (argumentProtocol (headers := headers) owner callerPrefix) conditionGate origin functions :=
  { entry with initial := ⟨entry.initial, globals⟩ }

/-- The actual wrapped body post supplies the same complete base pool. -/
theorem preserves_of_canonical {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := argumentProtocol (headers := headers) owner callerPrefix)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner callerPrefix entry globals) size) :
    CallableRuntimeBodyEntryContracts.PreservesAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro outcome after trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

/-- Native completion retains its independent Source grade and actual post pool. -/
theorem reflects_of_canonical {size : Nat}
    (meaning : CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := argumentProtocol (headers := headers) owner callerPrefix)
      (conditionGate := conditionGate) (origin := origin) functions program
      (wrap functions owner callerPrefix entry globals) size) :
    CallableRuntimeBodyEntryContracts.ReflectsAt
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (protocol := protocol headers keys) (conditionGate := conditionGate) (origin := origin)
      functions program entry size := by
  intro value finalStore completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned, related⟩ := meaning completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, returned.val, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBodyCanonicalEntries
