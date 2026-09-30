import Solcore.Core.Safety

/-! World-indexed stores for higher-order values and cyclic references. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Every location is typed against the same world. References are checked by
world lookup rather than by recursively following the store. -/
structure RuntimeStoreHasTypes
    (world : StoreTyping) (store : Store)
    (definitions : DataEnvironment := []) : Prop where
  length_eq : world.length = store.length
  lookup :
    ∀ {location : Location} {elementType : Ty},
      world[location]? = some elementType →
      ∃ value,
        store.read? location = some value ∧
        RuntimeValueHasType world value elementType definitions

namespace RuntimeStoreHasTypes

theorem nil (definitions : DataEnvironment := []) :
    RuntimeStoreHasTypes [] [] definitions where
  length_eq := rfl
  lookup := by simp

theorem read
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    ∃ value,
      store.read? location = some value ∧
      RuntimeValueHasType world value elementType definitions :=
  typing.lookup found

theorem location_lt
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty}
    (found : world[location]? = some elementType) :
    location < store.length := by
  have bound := (List.getElem?_eq_some_iff.mp found).1
  simpa [← typing.length_eq] using bound

theorem allocate
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {elementType : Ty} {value : Value}
    (valueTyping : RuntimeValueHasType world value elementType definitions) :
    RuntimeStoreHasTypes (world ++ [elementType])
      (store.allocate value).1 definitions := by
  have extension : WorldExtends world (world ++ [elementType]) :=
    ⟨[elementType], rfl⟩
  constructor
  · simp [typing.length_eq]
  · intro location storedType foundType
    by_cases old : location < world.length
    · have oldType : world[location]? = some storedType := by
        rw [List.getElem?_append_left (l₂ := [elementType]) old] at foundType
        exact foundType
      obtain ⟨oldValue, oldLookup, oldTyping⟩ := typing.lookup oldType
      have storeOld : location < store.length := by
        simpa [← typing.length_eq] using old
      exact ⟨oldValue,
        (Store.allocate_old_lookup store value storeOld).trans oldLookup,
        oldTyping.weaken extension⟩
    · have locationEq : location = world.length := by
        have bound := (List.getElem?_eq_some_iff.mp foundType).1
        have upper : location ≤ world.length := by
          apply Nat.lt_succ_iff.mp
          simpa using bound
        exact Nat.le_antisymm upper (Nat.le_of_not_gt old)
      subst location
      have storedTypeEq : storedType = elementType := by
        exact (Option.some.inj (by simpa using foundType)).symm
      subst storedType
      exact ⟨value,
        by simpa [← typing.length_eq] using Store.allocate_fresh_lookup store value,
        valueTyping.weaken extension⟩

theorem write
    {definitions : DataEnvironment} {world : StoreTyping}
    {store updatedStore : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType)
    (valueTyping : RuntimeValueHasType world value elementType definitions)
    (written : store.write? location value = some updatedStore) :
    RuntimeStoreHasTypes world updatedStore definitions := by
  constructor
  · rw [Store.write?_preserves_length written]
    exact typing.length_eq
  · intro otherLocation otherType otherFound
    obtain ⟨oldValue, oldLookup, oldTyping⟩ := typing.lookup otherFound
    by_cases same : otherLocation = location
    · subst otherLocation
      have typeEq := Option.some.inj (found.symm.trans otherFound)
      subst otherType
      exact ⟨value, Store.write?_reads_written written, valueTyping⟩
    · exact ⟨oldValue,
        (Store.write?_preserves_other written same).trans oldLookup, oldTyping⟩

theorem write_exists
    {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typing : RuntimeStoreHasTypes world store definitions)
    {location : Location} {elementType : Ty} {value : Value}
    (found : world[location]? = some elementType) :
    ∃ updatedStore, store.write? location value = some updatedStore :=
  (Store.write?_success_iff store location value).2 (typing.location_lt found)

end RuntimeStoreHasTypes

/-- Existing first-order stores embed without changing their locations. -/
theorem StoreHasTypes.toRuntime
    {world : StoreTyping} {store : Store}
    (typing : StoreHasTypes world store)
    (definitions : DataEnvironment := []) :
    RuntimeStoreHasTypes world store definitions where
  length_eq := typing.length_eq
  lookup := by
    intro location elementType found
    obtain ⟨value, read, payload, valueTyping⟩ := typing.lookup found
    exact ⟨value, read, payload.runtimeValueHasType valueTyping definitions⟩

end Solcore.Core
