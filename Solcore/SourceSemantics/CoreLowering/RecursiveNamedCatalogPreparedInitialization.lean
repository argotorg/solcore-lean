import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedRows
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCachedSupport

/-! Actual preparation supplies the complete ordered lambda cache and global
signatures to the closed initialization proof. Source headers, their cached
ledger and empty source lexical contexts remain independent static receipts.
This factory does not attribute a source body from a native cache or decoder. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

def store (compiled : SourceCoreUnifiedCompilation.Compiled) : Store :=
  initialStore compiled.indexed.base.globals (RecursiveNamedCachedRows.rows compiled)
    compiled.indexed.ancestry.layout.frame

def environment (compiled : SourceCoreUnifiedCompilation.Compiled) : Environment :=
  initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame

theorem evaluates (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Evaluates [] [] (SourceCoreCallableIndexedFrames.allocate compiled.indexed.ancestry.layout.frame
      (SourceCoreRecursiveEntry.allocateGlobals compiled.indexed.base.globals.reverse
        (SourceCoreRecursiveEntry.installFunctions compiled.indexed.secondPass.closures (LanguageResult.success .unit))))
      (.inRight .word .unit) (store compiled) := by
  rw [RecursiveNamedCachedRows.exact_cache compiled]
  exact framed_bootstrap _ _ _ (RecursiveNamedCachedRows.ordered compiled)

theorem typed {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe) :
    ∃ world, RuntimeStoreHasTypes world (store compiled) compiled.indexed.layouts.definitions :=
  stored accepted (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled)

theorem supported_cached {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {slot : Nat} {code : Expr} (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    NativeExpressionContextSupport.supported code (compiled.indexed.base.globals.length + 1) = true := by
  obtain ⟨_, _, _, ⟨receipt⟩⟩ := RecursiveNamedCachedRows.cached_at compiled cached
  rw [receipt.emitted] at cached ⊢
  exact RecursiveNamedCachedSupport.cached_supported accepted (RecursiveNamedCachedRows.rows compiled)
    (RecursiveNamedCachedRows.exact_cache compiled) (RecursiveNamedCachedRows.ordered compiled) cached

/-- Completed original machines expose the same actual bootstrap result and
store, with no source execution or source catalog as a premise. -/
theorem completed_store {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ finalStore = store compiled := by
  obtain ⟨_, emitted⟩ := recipe_emitted accepted
  have expected := evaluates compiled
  rw [← emitted] at expected
  exact evaluation_deterministic (runStateful_evaluation_sound completed) expected

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])

include ledger sizes locals in
theorem authority {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions) :
    ∃ world, Nonempty (Authority headers
      (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
      0 [] world ⟨[]⟩ (store compiled)) :=
  RecursiveNamedCatalogInitialization.of_recipe compiled headers
    (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled) ledger
    (fun header _ => CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
    sizes locals accepted definitions

include ledger sizes locals in
theorem entry {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ (store compiled) ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ (store compiled) (environment compiled)) :=
  RecursiveNamedCatalogInitialization.initial_entry compiled headers
    (RecursiveNamedCachedRows.rows compiled) (RecursiveNamedCachedRows.exact_cache compiled)
    (RecursiveNamedCachedRows.ordered compiled) ledger
    (fun header _ => CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
    sizes locals accepted definitions functions registry

include ledger sizes locals in
theorem completed_entry {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ finalStore (environment compiled)) := by
  obtain ⟨result, storeEq⟩ := completed_store accepted completed
  rw [storeEq]
  exact ⟨result, entry compiled headers ledger sizes locals accepted definitions functions registry⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
