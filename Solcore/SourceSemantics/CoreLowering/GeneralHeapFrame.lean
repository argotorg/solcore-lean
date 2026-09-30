import Solcore.SourceSemantics.CoreLowering.GeneralHeap

/-! Source execution preserves existing administrative cells: they remain
outside the source map and retain their exact Core values. This is stronger
than the general runtime typing of the final store and keeps installed global
code available to later calls. Newly allocated cells are outside this frame. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.GeneralHeap

/-- Existing Core locations without a source alias keep their contents and
cannot become source aliases during this execution. -/
def AdministrativePreserved (mapping : LocationMap) (store : Core.Store)
    (futureMapping : LocationMap) (futureStore : Core.Store) : Prop :=
  ∀ location, location ∉ mapping → location < store.length →
    location ∉ futureMapping ∧ futureStore.read? location = store.read? location

namespace AdministrativePreserved

theorem refl (mapping : LocationMap) (store : Core.Store) : AdministrativePreserved mapping store mapping store := by
  intro location absent _
  exact ⟨absent, rfl⟩

theorem trans {firstMap secondMap thirdMap : LocationMap} {first second third : Core.Store}
    (left : AdministrativePreserved firstMap first secondMap second)
    (right : AdministrativePreserved secondMap second thirdMap third) :
    AdministrativePreserved firstMap first thirdMap third := by
  intro location absent bound
  obtain ⟨middleAbsent, same⟩ := left location absent bound
  have firstRead : first.read? location = some first[location] := List.getElem?_eq_getElem bound
  have middleBound : location < second.length :=
    (List.getElem?_eq_some_iff.mp (same.trans firstRead)).1
  obtain ⟨lastAbsent, lastSame⟩ := right location middleAbsent middleBound
  exact ⟨lastAbsent, lastSame.trans same⟩

theorem allocate (mapping : LocationMap) (store : Core.Store) (value : Core.Value) :
    AdministrativePreserved mapping store (mapping ++ [store.length]) (store.allocate value).1 := by
  intro location absent bound
  refine ⟨?_, Core.Store.allocate_old_lookup store value bound⟩
  simp only [List.mem_append, List.mem_singleton, not_or]
  exact ⟨absent, Nat.ne_of_lt bound⟩

theorem allocate_administrative (mapping : LocationMap) (store : Core.Store) (value : Core.Value) :
    AdministrativePreserved mapping store mapping (store.allocate value).1 := by
  intro location absent bound
  exact ⟨absent, Core.Store.allocate_old_lookup store value bound⟩

theorem write {mapping : LocationMap} {store updated : Core.Store}
    {location : Core.Location} {value : Core.Value}
    (mapped : location ∈ mapping) (written : store.write? location value = some updated) :
    AdministrativePreserved mapping store mapping updated := by
  intro other absent _
  have different : other ≠ location := by intro same; exact absent (same ▸ mapped)
  exact ⟨absent, Core.Store.write?_preserves_other written different⟩

end AdministrativePreserved

end Solcore.SourceSemantics.CoreLowering.GeneralHeap
