import Solcore.Frontend.TypeNameProperties

/-! Semantic extension retains every existing first-match type meaning.
New keys may gain meanings; only mutual extension preserves lookup absence. -/

set_option autoImplicit false

namespace Solcore.Frontend

namespace TypeNameTable

/-- Preserve original meanings, not merely membership in the list of entries. -/
def Extends (old next : TypeNameTable) : Prop :=
  ∀ {key type}, Lookup old key type → Lookup next key type

theorem Extends.refl (table : TypeNameTable) : Extends table table := by
  intro key type found
  exact found

theorem Extends.trans {old middle next : TypeNameTable}
    (first : Extends old middle) (second : Extends middle next) : Extends old next := by
  intro key type found
  exact second (first found)

/-- Later duplicate entries cannot override the first original match. -/
theorem Extends.append_right (table extras : TypeNameTable) : Extends table (table ++ extras) := by
  intro key type found
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

/-- Freshness is sufficient, not necessary: a same-meaning duplicate can also
be safe, but a prefix that changes an existing meaning is not an extension. -/
theorem Extends.cons_fresh (table : TypeNameTable) (key : List String) (type : Core.Ty)
    (fresh : key ∉ table.map Prod.fst) : Extends table ((key, type) :: table) := by
  intro original originalType found
  apply Lookup.tail ?_ found
  intro same
  apply fresh
  rw [same]
  exact List.mem_map.mpr ⟨(original, originalType), found.mem, rfl⟩

theorem lookup?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : Extends left right) (backward : Extends right left) (key : List String) :
    lookup? left key = lookup? right key := by
  cases leftResult : lookup? left key with
  | none =>
      cases rightResult : lookup? right key with
      | none => rfl
      | some type =>
          have accepted := lookup?_iff.mpr (backward (lookup?_iff.mp rightResult))
          rw [leftResult] at accepted
          cases accepted
  | some type => exact (lookup?_iff.mpr (forward (lookup?_iff.mp leftResult))).symm

end TypeNameTable

theorem TypeNameDenotes.extend_types {old next : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : TypeNameDenotes old source type)
    (extension : TypeNameTable.Extends old next) : TypeNameDenotes next source type := by
  cases meaning with
  | named found => exact .named (extension found)

theorem interpretTypeName?_some_of_extends {old next : TypeNameTable}
    (extension : TypeNameTable.Extends old next) {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretTypeName? old source = some type) :
    interpretTypeName? next source = some type :=
  ((interpretTypeName?_sound accepted).extend_types extension).complete

theorem interpretTypeName?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : TypeNameTable.Extends left right) (backward : TypeNameTable.Extends right left)
    (source : Syntax.TypeExpr) : interpretTypeName? left source = interpretTypeName? right source := by
  rcases source with ⟨span, payload⟩
  cases payload <;> try rfl
  case named name arguments =>
    cases arguments with
    | none => exact TypeNameTable.lookup?_eq_of_mutual_extends forward backward _
    | some _ => rfl

end Solcore.Frontend
