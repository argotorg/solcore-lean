import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.GenericCellHeap
import Solcore.SourceSemantics.CoreLowering.RecursivePublicApplicationResult

/-! Direct public application retains the full returned caller and heap.
The accepted execution receipt remains separate from this semantic post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Result
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)

/-- The full actual returned caller and semantic result of direct application.
Native execution is supplied separately by the accepted public checkpoint. -/
def ResultAt (context : SourceSemantics.Context) (sourceResult : TypeSystem.Ty)
    (nativeResult : Core.Ty) (outcome : Staging.Recursive.Outcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  RecursiveStageMeaning.ResultRepresentsFor
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld sourceResult nativeResult faults outcome value ∧
  GenericHeap.CellHeapRepresents cells
    finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    Relates caller returned ∧
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      CallableIndexedOwnedBodyRestorationAdmission.bridge context sourceResult outcome returned

variable {functions cells caller} {context : SourceSemantics.Context}
  {sourceResult : TypeSystem.Ty} {nativeResult : Core.Ty}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- Actual successful decoding exposes the Source value and current heap,
including all retained captured cells and the exact native world. -/
theorem returned_value
    (result : ResultAt (registry := registry) functions cells caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧
      ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        sourceResult source payload nativeResult ∧
      GenericHeap.CellHeapRepresents cells
        finalMap finalWorld after finalStore ∧
      finalWorld = finalStore.map Value.type ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧ StableRows returned ∧
        Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after source sourceResult := by
  obtain ⟨represented, heaps, _maps, _worlds, _administrative, _metadata,
    returned, related, post⟩ := result
  cases represented with
  | value represented =>
      simp only [LanguageResult.decode?, Option.some.injEq, LanguageResult.Outcome.succeeded.injEq] at decoded
      subst payload
      have admission := CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission.at_value post
      exact ⟨_, rfl, represented, heaps, heaps.runtime_hasTypes.world_eq,
        returned, related, admission.2.rows, admission.2.heap, admission.1⟩
  | fault represented => cases decoded
theorem ResultAt.includes
    {other : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions}
    (included : ∀ {cell value payload}, cells.Represents finalMap finalWorld cell value payload →
      other.Represents finalMap finalWorld cell value payload)
    (result : ResultAt (registry := registry) functions cells caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults) :
    ResultAt (registry := registry) functions other caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, result.2.1.includes included, result.2.2⟩

theorem ResultAt.ordinary_iff :
    ResultAt (registry := registry) functions
      (GenericHeap.CellModel.ordinary (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
      caller context sourceResult nativeResult outcome after native finalStore finalMap finalWorld faults ↔
    RecursivePublicApplicationResult.ResultAt (registry := registry) functions caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults := by
  simp only [ResultAt, RecursivePublicApplicationResult.ResultAt, GenericHeap.ordinaryHeap_iff,
    CompatibleAmbientHeap.HeapRepresents]
end Result

section Named
open CallableIndexedOwnedFunctionValues (Header NamedCapture OwnedKey)
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (cells : GenericHeap.CellModel (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  (arguments : List Core.Value)

def NamedResultAt (context : SourceSemantics.Context) (outcome : Staging.Recursive.Outcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) (faults : RecursiveStageMeaning.FaultRep) : Prop :=
  Evaluates (DataPatternValues.packValues arguments :: capture.captured) store
    (header.code.rename capture.embedding.lift) value finalStore ∧
  ResultAt (registry := registry) functions cells caller context header.function.resultType header.output
    outcome after value finalStore finalMap finalWorld faults

variable {functions cells owner caller header capture arguments}
  {context : SourceSemantics.Context} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

theorem named_returned_value
    (result : NamedResultAt (registry := registry) functions cells owner caller header capture arguments
      context outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧
      ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        header.function.resultType source payload header.output ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      finalWorld = finalStore.map Value.type ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧ StableRows returned ∧ Dynamic.HeapWellTyped context after ∧
        Dynamic.ValueHasType context after source header.function.resultType :=
  returned_value result.2 decoded

theorem NamedResultAt.ordinary_iff :
    NamedResultAt (registry := registry) functions
      (GenericHeap.CellModel.ordinary (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
      owner caller header capture arguments context outcome after native finalStore finalMap finalWorld faults ↔
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt (registry := registry)
      (payloads := arguments) functions owner caller header capture context outcome after native finalStore finalMap finalWorld faults := by
  simp only [NamedResultAt, ResultAt, CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt,
    GenericHeap.ordinaryHeap_iff, CompatibleAmbientHeap.HeapRepresents]
end Named

end Solcore.SourceSemantics.CoreLowering.CellAwarePublicApplicationResult
