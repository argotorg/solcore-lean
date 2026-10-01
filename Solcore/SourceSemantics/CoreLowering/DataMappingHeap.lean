import Solcore.SourceSemantics.CoreLowering.GenericHeap
import Solcore.SourceSemantics.CoreLowering.DataMappingComparison

/-! Mapping helpers extend the existing generic heap relation. They neither
create source aliases for administrative closures nor change source cells.
Runtime typing supplies the extended world, including cyclic closures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMappingHeap
open Core Frontend GeneralHeap GenericHeap

theorem heap_append {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {model : PayloadModel catalog projects}
    {mapping : LocationMap} {world futureWorld : StoreTyping} {heap : Dynamic.Heap} {store suffix : Store}
    (related : HeapRepresents model mapping world heap store)
    (extension : WorldExtends world futureWorld)
    (typed : RuntimeStoreHasTypes futureWorld (store ++ suffix) catalog.definitions) :
    HeapRepresents model mapping futureWorld heap (store ++ suffix) := by
  refine ⟨related.length_eq, related.injective, typed, ?_⟩
  intro source target mapped
  obtain ⟨cell, value, payload, sourceRead, typeRead, coreRead, represented⟩ := related.cells mapped
  exact ⟨cell, value, payload, sourceRead, extension.lookup typeRead,
    by simpa [Store.read?, List.getElem?_append_left (related.target_lt mapped)] using coreRead,
    represented.extend (.refl _) extension⟩

theorem administrative_append (mapping : LocationMap) (store suffix : Store) :
    AdministrativePreserved mapping store mapping (store ++ suffix) := by
  intro location absent bound
  exact ⟨absent, by simp [Store.read?, List.getElem?_append_left bound]⟩

/-- Combine a proved finite helper evaluation and its exact store suffix with
the actual Core typing proof. The source heap and map remain unchanged. -/
theorem evaluation_preserves_frame {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {model : PayloadModel catalog projects}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store finalStore : Store}
    (related : HeapRepresents model mapping world heap store)
    {environment : Environment} {context : Core.Context} {expression : Expr} {value : Value} {type : Ty}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions)
    (expressionTyped : HasType context expression type catalog.definitions)
    (evaluated : Evaluates environment store expression value finalStore)
    {suffix : Store} (extended : finalStore = store ++ suffix) :
    ∃ futureWorld, WorldExtends world futureWorld ∧ HeapRepresents model mapping futureWorld heap finalStore ∧
      RuntimeValueHasType futureWorld value type catalog.definitions ∧
      AdministrativePreserved mapping store mapping finalStore := by
  subst finalStore
  obtain ⟨futureWorld, extension, storeTyped, valueTyped⟩ :=
    evaluation_preserves_type evaluated expressionTyped environmentTyped related.runtime_hasTypes
  exact ⟨futureWorld, extension, heap_append related extension storeTyped, valueTyped,
    administrative_append mapping store suffix⟩

end Solcore.SourceSemantics.CoreLowering.DataMappingHeap
