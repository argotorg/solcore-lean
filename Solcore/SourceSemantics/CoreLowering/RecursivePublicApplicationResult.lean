import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds

/-! Direct public application retains the full returned caller and heap.
The accepted execution receipt remains separate from this semantic post. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursivePublicApplicationResult
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Result
variable (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
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
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
    finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    Relates caller returned ∧
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
      CallableIndexedOwnedBodyRestorationAdmission.bridge context sourceResult outcome returned

variable {functions caller} {context : SourceSemantics.Context}
  {sourceResult : TypeSystem.Ty} {nativeResult : Core.Ty}
  {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
  {native payload : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep}

/-- Actual successful decoding exposes the Source value and current heap,
including all retained captured cells and the exact native world. -/
theorem returned_value
    (result : ResultAt (registry := registry) functions caller context sourceResult nativeResult
      outcome after native finalStore finalMap finalWorld faults)
    (decoded : LanguageResult.decode? native = some (.succeeded payload)) :
    ∃ source, outcome = .value source ∧
      ValueRep compiled.compatible.checked registry functions finalMap finalWorld
        sourceResult source payload nativeResult ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
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
end Result

end Solcore.SourceSemantics.CoreLowering.RecursivePublicApplicationResult
