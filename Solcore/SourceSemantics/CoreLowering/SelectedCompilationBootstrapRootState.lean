import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitializationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads

/-! The actual bootstrap constructs the owned state used by the public root.
The key is fixed before choosing a function model: initialized globals, no
capture prefix, and physical frame zero. Native completion fixes the complete
store, and store typing fixes the exact world. The original stored authority
supplies empty stable history, source heap representation and global reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBootstrapRootState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

/-- The real initial frame is at zero; each global keeps its prepared slot. -/
def key (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Key compiled (Program.ofChecked compiled.sourceProgram) :=
  ⟨(fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot), 0, 0⟩

def keys (compiled : SourceCoreUnifiedCompilation.Compiled) :
    List (Key compiled (Program.ofChecked compiled.sourceProgram)) := [key compiled]

def owner (compiled : SourceCoreUnifiedCompilation.Compiled) : OwnedKey (keys compiled) :=
  ⟨⟨0, by simp [keys]⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}

/-- The original entry constructor retains the empty histories omitted by the
older existential bootstrap packet. Its actual native typing fixes the world. -/
private theorem initial
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (ledger : RecursiveNamedCatalog.Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ caller : State headers (keys compiled)
        ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type,
          ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
          SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
        ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type) ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      (∀ header, header ∈ headers →
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
          some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
            ((owner compiled).key.locations header))) ∧
      (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨world, entry, heaps, receipt⟩ :=
    RecursiveNamedCatalogPreparedInitializationReceipts.entry_with_constructor
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) compiled headers
      ledger sizes locals accepted rfl functions registry
  have worldEq := heaps.runtime_hasTypes.world_eq
  subst world
  let row : CallableIndexedAuthorityPool.EntryValid
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers (key compiled) []
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type) ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) := by
    refine { authority := entry.authority, frame_eq := ?_ }
    change entry.authority.frameLocation = 0
    exact receipt.frameLocation
  let caller : State headers (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
    CallableIndexedAuthorityPool.Pool.singleton row
  refine ⟨caller, ?_, heaps, ?_, ?_⟩
  · intro selected
    have same : selected = (owner compiled).position := by
      apply Fin.ext
      have bound := selected.isLt
      change selected.val < 1 at bound
      change selected.val = 0
      omega
    subst selected
    change ∃ metadata, Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table entry.authority.current entry.authority.ghost metadata
    rw [receipt.current, receipt.ghost]
    exact ⟨none, .empty⟩
  · intro header member
    have reference : (RecursiveNamedCatalogPreparedInitialization.environment compiled)[header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
        (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)) := by
      simpa only [List.length_nil, Nat.zero_add] using entry.globals header member
    rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at reference
    exact reference
  · intro context cell member
    exact nomatch member

/-- Accepted finite rows derive their ledger, global sizes and empty locals.
The actual completed bootstrap fixes the returned native store before the
owned state is constructed. No initial pool, stable-row or heap law is supplied. -/
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
      ∃ caller : State (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys compiled)
          ⟨[], [], finalStore.map Value.type, ⟨[]⟩, finalStore,
            SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
        CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
          (finalStore.map Value.type) ⟨[]⟩ finalStore ∧
        (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
          (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
            some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
              ((owner compiled).key.locations header))) ∧
        (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨result, storeEq⟩ := RecursiveNamedCatalogPreparedInitialization.completed_store accepted completed
  refine ⟨result, storeEq, ?_⟩
  rw [storeEq]
  exact initial accepted
    (show RecursiveNamedCatalog.Ledger (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) compiled.indexed.secondPass.closures from
      ⟨by rw [CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.slots inputs rows]; exact distinct,
       bodyTyping.function_ids, CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.cache inputs rows⟩)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.globals rows)
    (CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.empty_locals inputs rows)
    functions registry

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBootstrapRootState
