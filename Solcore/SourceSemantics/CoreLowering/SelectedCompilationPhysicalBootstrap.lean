import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedPhysicalCaptures

/-! Actual finite ordinary inputs and the completed native bootstrap establish
both the old semantic pool and every physical cache row, including methods.
No complete ordinary Header inventory or body execution premise is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBootstrap
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The finite bootstrap owner's association is the actual installed layout. -/
theorem key_physical (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))) :
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical (owner compiled).key headers := by
  constructor
  · rfl
  · rfl
  · intro header _member
    rfl

theorem of_completed
    (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧
      finalStore = RecursiveNamedCatalogPreparedInitialization.store compiled ∧
      ∃ caller : (CallableIndexedOwnedPhysicalCanonicalState.protocol
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys compiled) 0).State
          ⟨[], [], finalStore.map Value.type, ⟨[]⟩, finalStore,
            SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
        CallableIndexedOwnedIndirectExpressionHeads.StableRows caller.base.val ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
          (finalStore.map Value.type) ⟨[]⟩ finalStore ∧
        (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
          (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
            some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
              ((owner compiled).key.locations header))) ∧
        (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨valueEq, storeEq, caller, stable, heaps, globals, sourceTyped⟩ :=
    SelectedCompilationBootstrapRootState.of_completed bodyTyping inputs rows accepted distinct functions registry completed
  refine ⟨valueEq, storeEq, ⟨⟨caller, CallableIndexedOwnedPhysicalGlobals.environment_slots compiled⟩,
    CallableIndexedOwnedPhysicalGlobals.of_completed accepted completed⟩, stable, heaps, globals, sourceTyped⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBootstrap
