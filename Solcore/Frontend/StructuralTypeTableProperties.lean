import Solcore.Frontend.StructuralTypeProperties
import Solcore.Frontend.TypeNameTableExtensionProperties

/-! Structural interpretation depends on first-match named-leaf meanings.
One-way extension preserves successful results; only lookup equality or mutual
extension preserves the entire optional result, including rejection. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem StructuralTypeDenotes.extend_types {old next : TypeNameTable}
    {source : Syntax.TypeExpr} {type : Core.Ty} (meaning : StructuralTypeDenotes old source type)
    (extension : TypeNameTable.Extends old next) : StructuralTypeDenotes next source type := by
  induction meaning with
  | named found => exact .named (extension found)
  | unit => exact .unit
  | single _ ih => exact .single ih
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH

theorem interpretStructuralType?_some_of_extends {old next : TypeNameTable}
    (extension : TypeNameTable.Extends old next) {source : Syntax.TypeExpr} {type : Core.Ty}
    (accepted : interpretStructuralType? old source = some type) :
    interpretStructuralType? next source = some type :=
  ((interpretStructuralType?_sound accepted).extend_types extension).complete

/-- Equality of every visible lookup, not row membership or uniqueness, is enough.
Hidden duplicate entries, table lengths and source occurrence ranges are unrestricted. -/
theorem interpretStructuralType?_congr_lookup (left right : TypeNameTable)
    (sameLookup : ∀ key, left.lookup? key = right.lookup? key) (source : Syntax.TypeExpr) :
    interpretStructuralType? left source = interpretStructuralType? right source := by
  have forward : TypeNameTable.Extends left right := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [← sameLookup key]
    exact TypeNameTable.lookup?_iff.mpr found
  have backward : TypeNameTable.Extends right left := by
    intro key type found
    apply TypeNameTable.lookup?_iff.mp
    rw [sameLookup key]
    exact TypeNameTable.lookup?_iff.mpr found
  cases leftResult : interpretStructuralType? left source with
  | none =>
      cases rightResult : interpretStructuralType? right source with
      | none => rfl
      | some type =>
          have accepted := interpretStructuralType?_some_of_extends backward rightResult
          rw [leftResult] at accepted
          cases accepted
  | some type => exact (interpretStructuralType?_some_of_extends forward leftResult).symm

theorem interpretStructuralType?_eq_of_mutual_extends {left right : TypeNameTable}
    (forward : TypeNameTable.Extends left right) (backward : TypeNameTable.Extends right left)
    (source : Syntax.TypeExpr) : interpretStructuralType? left source = interpretStructuralType? right source :=
  interpretStructuralType?_congr_lookup left right
    (TypeNameTable.lookup?_eq_of_mutual_extends forward backward) source

end Solcore.Frontend
