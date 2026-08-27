import Solcore.Core.Syntax

set_option autoImplicit false

namespace Solcore.Core

namespace Store

def allocate (store : Store) (value : Value) : Store × Location :=
  (store ++ [value], store.length)

def read? (store : Store) (location : Location) : Option Value :=
  store[location]?

def write?
    (store : Store)
    (location : Location)
    (value : Value) : Option Store :=
  if location < store.length then
    some (store.set location value)
  else
    none

@[simp]
theorem allocate_updatedStore
    (store : Store)
    (value : Value) :
    (store.allocate value).1 = store ++ [value] :=
  rfl

@[simp]
theorem allocate_freshLocation
    (store : Store)
    (value : Value) :
    (store.allocate value).2 = store.length :=
  rfl

@[simp]
theorem allocate_length
    (store : Store)
    (value : Value) :
    (store.allocate value).1.length = store.length + 1 := by
  simp [allocate]

@[simp]
theorem allocate_fresh_lookup
    (store : Store)
    (value : Value) :
    (store.allocate value).1.read? (store.allocate value).2 = some value := by
  simp [allocate, read?]

@[simp]
theorem allocate_fresh_absent
    (store : Store)
    (value : Value) :
    store.read? (store.allocate value).2 = none := by
  simp [allocate, read?]

theorem allocate_old_lookup
    (store : Store)
    (value : Value)
    {location : Location}
    (inBounds : location < store.length) :
    (store.allocate value).1.read? location = store.read? location := by
  simpa [allocate, read?] using
    (List.getElem?_append_left (l₂ := [value]) inBounds)

theorem write?_eq_some_iff
    {store updatedStore : Store}
    {location : Location}
    {value : Value} :
    store.write? location value = some updatedStore ↔
      location < store.length ∧ updatedStore = store.set location value := by
  by_cases inBounds : location < store.length <;>
    simp [write?, inBounds, eq_comm]

theorem write?_success_iff
    (store : Store)
    (location : Location)
    (value : Value) :
    (∃ updatedStore, store.write? location value = some updatedStore) ↔
      location < store.length := by
  constructor
  · rintro ⟨updatedStore, written⟩
    exact (write?_eq_some_iff.mp written).1
  · intro inBounds
    exact ⟨store.set location value,
      write?_eq_some_iff.mpr ⟨inBounds, rfl⟩⟩

@[simp]
theorem write?_failure_iff
    (store : Store)
    (location : Location)
    (value : Value) :
    store.write? location value = none ↔ store.length ≤ location := by
  simp [write?, Nat.not_lt]

theorem write?_preserves_length
    {store updatedStore : Store}
    {location : Location}
    {value : Value}
    (written : store.write? location value = some updatedStore) :
    updatedStore.length = store.length := by
  rw [(write?_eq_some_iff.mp written).2]
  exact List.length_set

theorem write?_reads_written
    {store updatedStore : Store}
    {location : Location}
    {value : Value}
    (written : store.write? location value = some updatedStore) :
    updatedStore.read? location = some value := by
  obtain ⟨inBounds, rfl⟩ := write?_eq_some_iff.mp written
  simp [read?, inBounds]

theorem write?_preserves_other
    {store updatedStore : Store}
    {location otherLocation : Location}
    {value : Value}
    (written : store.write? location value = some updatedStore)
    (different : otherLocation ≠ location) :
    updatedStore.read? otherLocation = store.read? otherLocation := by
  obtain ⟨_, rfl⟩ := write?_eq_some_iff.mp written
  simp [read?, Ne.symm different]

end Store

end Solcore.Core
