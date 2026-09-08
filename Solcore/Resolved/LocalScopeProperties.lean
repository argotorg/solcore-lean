import Solcore.Resolved.LocalScope

/-! Executable local-table lookup agrees with independent first-occurrence
witnesses and positional projection. Malformed duplicate identities still
have deterministic first-match behavior; no freshness policy is assumed. -/

set_option autoImplicit false

namespace Solcore.Resolved.LocalScope

theorem lookup?_iff {α : Type} {scope : LocalScope α} {id : LocalId} {value : α} :
    lookup? scope id = some value ↔ Lookup scope id value := by
  constructor
  · intro result
    induction scope with
    | nil => simp [lookup?] at result
    | cons entry rest ih =>
        rcases entry with ⟨candidate, entryValue⟩
        by_cases same : candidate = id
        · subst candidate
          simp only [lookup?, ↓reduceIte, Option.some.injEq] at result
          subst entryValue
          exact .head
        · exact .tail same (ih (by simpa only [lookup?, if_neg same] using result))
  · intro found
    induction found with
    | head => simp [lookup?]
    | tail different found ih => simpa only [lookup?, if_neg different] using ih

theorem index?_iff {scope : List LocalId} {id : LocalId} {index : Nat} :
    index? scope id = some index ↔ IndexOf scope id index := by
  constructor
  · intro result
    induction scope generalizing index with
    | nil => simp [index?] at result
    | cons candidate rest ih =>
        by_cases same : candidate = id
        · subst candidate
          simp only [index?, ↓reduceIte, Option.some.injEq] at result
          subst index
          exact .head
        · cases tailResult : index? rest id with
          | none => simp [index?, same, tailResult] at result
          | some next =>
              simp only [index?, if_neg same, tailResult, Option.map_some, Option.some.injEq] at result
              subst index
              exact .tail same (ih tailResult)
  · intro found
    induction found with
    | head => simp [index?]
    | tail different found ih => simp only [index?, if_neg different, ih, Option.map_some]

theorem Lookup.indexed {α : Type} {scope : LocalScope α} {id : LocalId} {value : α}
    (found : Lookup scope id value) :
    ∃ index, IndexOf (ids scope) id index ∧ (values scope)[index]? = some value := by
  induction found with
  | head => exact ⟨0, .head, rfl⟩
  | tail different found ih =>
      rcases ih with ⟨index, indexed, atValue⟩
      exact ⟨index + 1, .tail different indexed, atValue⟩

theorem lookup_of_indexed {α : Type} {scope : LocalScope α} {id : LocalId} {index : Nat} {value : α}
    (indexed : IndexOf (ids scope) id index) (atValue : (values scope)[index]? = some value) :
    Lookup scope id value := by
  induction scope generalizing index with
  | nil => cases indexed
  | cons entry rest ih =>
      rcases entry with ⟨candidate, entryValue⟩
      cases indexed with
      | head =>
          change some entryValue = some value at atValue
          cases atValue
          exact .head
      | tail different indexed => exact .tail different (ih indexed atValue)

theorem index_lookup {α : Type} {scope : LocalScope α} {id : LocalId} {value : α} :
    lookup? scope id = some value ↔
      ∃ index, index? (ids scope) id = some index ∧ (values scope)[index]? = some value := by
  constructor
  · intro result
    rcases (lookup?_iff.mp result).indexed with ⟨index, indexed, atValue⟩
    exact ⟨index, index?_iff.mpr indexed, atValue⟩
  · rintro ⟨index, indexed, atValue⟩
    exact lookup?_iff.mpr (lookup_of_indexed (index?_iff.mp indexed) atValue)

theorem Lookup.value_unique {α : Type} {scope : LocalScope α} {id : LocalId} {left right : α}
    (leftFound : Lookup scope id left) (rightFound : Lookup scope id right) : left = right :=
  Option.some.inj ((lookup?_iff.mpr leftFound).symm.trans (lookup?_iff.mpr rightFound))

theorem IndexOf.index_unique {scope : List LocalId} {id : LocalId} {left right : Nat}
    (leftFound : IndexOf scope id left) (rightFound : IndexOf scope id right) : left = right :=
  Option.some.inj ((index?_iff.mpr leftFound).symm.trans (index?_iff.mpr rightFound))

theorem lookup_iff_getElem? {α : Type} {scope : LocalScope α} {id : LocalId} {index : Nat} {value : α}
    (indexed : IndexOf (ids scope) id index) :
    Lookup scope id value ↔ (values scope)[index]? = some value := by
  constructor
  · intro found
    rcases found.indexed with ⟨actual, actualIndex, atValue⟩
    cases actualIndex.index_unique indexed
    exact atValue
  · exact lookup_of_indexed indexed

theorem IndexOf.getElem? {scope : List LocalId} {id : LocalId} {index : Nat}
    (found : IndexOf scope id index) : scope[index]? = some id := by
  induction found with
  | head => rfl
  | tail _ _ ih => exact ih

theorem IndexOf.lt_length {scope : List LocalId} {id : LocalId} {index : Nat}
    (found : IndexOf scope id index) : index < scope.length := by
  induction found with
  | head => simp
  | tail _ _ ih => simpa only [List.length_cons] using Nat.succ_lt_succ ih

theorem Lookup.mem {α : Type} {scope : LocalScope α} {id : LocalId} {value : α}
    (found : Lookup scope id value) : (id, value) ∈ scope := by
  induction found with
  | head => exact List.mem_cons_self
  | tail _ _ ih => exact List.mem_cons_of_mem _ ih

theorem index?_eq_none_iff {scope : List LocalId} {id : LocalId} :
    index? scope id = none ↔ id ∉ scope := by
  induction scope with
  | nil => simp [index?]
  | cons candidate rest ih =>
      by_cases same : candidate = id
      · subst candidate; simp [index?]
      · simp [index?, same, Ne.symm same, ih]

theorem lookup?_eq_none_iff {α : Type} {scope : LocalScope α} {id : LocalId} :
    lookup? scope id = none ↔ id ∉ ids scope := by
  induction scope with
  | nil => simp [lookup?, ids]
  | cons entry rest ih =>
      rcases entry with ⟨candidate, entryValue⟩
      by_cases same : candidate = id
      · subst candidate; simp [lookup?, ids]
      · simpa [lookup?, same, ids, Ne.symm same] using ih

theorem ids_length {α : Type} (scope : LocalScope α) : (ids scope).length = scope.length := by
  simp only [ids, List.length_map]

theorem values_length {α : Type} (scope : LocalScope α) : (values scope).length = scope.length := by
  simp only [values, List.length_map]

end Solcore.Resolved.LocalScope
