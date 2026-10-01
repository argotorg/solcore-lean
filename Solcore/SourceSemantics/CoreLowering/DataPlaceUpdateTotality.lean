import Solcore.SourceSemantics.Dynamic.Place

/-! A readable independent projection path can install a fixed replacement.
This is a structural source theorem: it does not evaluate a compiler or compare
Core values, and first-match lookup determines the replaced mapping position. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTotality
open Solcore.SourceSemantics.Dynamic

private theorem replace_found {key selected replacement : Value} {entries : List (Value × Value)}
    (found : MappingLookup key entries selected) : ∃ updated, MappingUpdate key replacement entries updated := by
  induction found with
  | head equal => exact ⟨_, .head equal⟩
  | tail different found ih => obtain ⟨updated, changed⟩ := ih; exact ⟨_, .tail different changed⟩

private theorem replace_at {values : List Value} {index : Nat} {selected replacement : Value}
    (found : ValueAt values index selected) : ∃ updated, ValuesReplaceAt values index replacement updated := by
  induction found with
  | head => exact ⟨_, .head⟩
  | tail found ih => obtain ⟨updated, changed⟩ := ih; exact ⟨_, .tail changed⟩

/-- Every selected path supports one fixed, already computed replacement. The
replacement never affects key evaluation or reconstruction of earlier nodes. -/
theorem read_update {initial selected : Option Value} {projections : List EvaluatedProjection}
    (read : ProjectionsRead initial projections selected) (replacement : Value) :
    ∃ updated, ProjectionsUpdate (fun _ value => value = replacement) initial projections updated := by
  induction read with
  | nil => exact ⟨replacement, .leaf rfl⟩
  | indexFound found read ih =>
    obtain ⟨child, changed⟩ := ih
    obtain ⟨entries, inserted⟩ := replace_found (replacement := child) found
    exact ⟨_, .indexFound found changed (.update inserted)⟩
  | indexDefault absent defaulted read ih =>
    obtain ⟨child, changed⟩ := ih
    exact ⟨_, .indexDefault absent defaulted changed (.append absent)⟩
  | member found read ih =>
    obtain ⟨child, changed⟩ := ih
    obtain ⟨values, replaced⟩ := replace_at (replacement := child) found
    exact ⟨_, .member found changed replaced⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceUpdateTotality
