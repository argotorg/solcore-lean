import Solcore.Frontend.LocalReferenceProperties

/-! Relabel only the IDs in an explicit ordered name table. Spellings, row
order, and first-name-match behavior are unchanged, even for noninjective maps.
This is not source spelling renaming or a fresh-identity allocation policy. -/

set_option autoImplicit false

namespace Solcore.Frontend.LocalNameTable

def mapIds (mapping : Resolved.LocalId → Resolved.LocalId) (table : LocalNameTable) :
    LocalNameTable :=
  table.map (fun entry => (entry.1, mapping entry.2))

@[simp] theorem mapIds_id (table : LocalNameTable) : mapIds id table = table := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, id⟩
      simp only [mapIds, List.map_cons] at ih ⊢
      exact congrArg (List.cons (name, id)) ih

theorem mapIds_comp (table : LocalNameTable)
    (first second : Resolved.LocalId → Resolved.LocalId) :
    mapIds second (mapIds first table) = mapIds (second ∘ first) table := by
  simp only [mapIds, List.map_map, Function.comp_def]

/-- Name lookup selects the same row; no injectivity premise is necessary. -/
theorem lookup?_mapIds (mapping : Resolved.LocalId → Resolved.LocalId)
    (table : LocalNameTable) (spelling : String) :
    lookup? (mapIds mapping table) spelling = (lookup? table spelling).map mapping := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, id⟩
      by_cases same : candidate = spelling
      · simp only [mapIds, List.map_cons, lookup?, if_pos same, Option.map_some]
      · simpa only [mapIds, List.map_cons, lookup?, if_neg same] using ih

theorem lookup_mapIds_iff_exists (mapping : Resolved.LocalId → Resolved.LocalId)
    {table : LocalNameTable} {spelling : String} {renamed : Resolved.LocalId} :
    Lookup (mapIds mapping table) spelling renamed ↔
      ∃ original, Lookup table spelling original ∧ mapping original = renamed := by
  simp only [← lookup?_iff, lookup?_mapIds, Option.map_eq_some_iff]

theorem lookup_mapIds_iff (mapping : Resolved.LocalId → Resolved.LocalId)
    (injective : Function.Injective mapping)
    {table : LocalNameTable} {spelling : String} {id : Resolved.LocalId} :
    Lookup (mapIds mapping table) spelling (mapping id) ↔ Lookup table spelling id := by
  rw [lookup_mapIds_iff_exists]
  constructor
  · rintro ⟨original, found, same⟩
    cases injective same
    exact found
  · intro found
    exact ⟨id, found, rfl⟩

end Solcore.Frontend.LocalNameTable
