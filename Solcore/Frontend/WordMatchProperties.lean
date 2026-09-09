import Solcore.Frontend.WordMatch
import Solcore.Frontend.WordLiteralProperties

/-! Independent pattern meaning and original ordered choice are deterministic.
No checker, lowering, typing or Core execution assumption is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem WordMatchPatternDenotes.value_unique {pattern : Syntax.Pattern} {left right : Core.Word}
    (first : WordMatchPatternDenotes pattern left)
    (second : WordMatchPatternDenotes pattern right) : left = right := by
  obtain ⟨leftLiteral, leftShape, leftMeaning⟩ := first
  obtain ⟨rightLiteral, rightShape, rightMeaning⟩ := second
  have literals := Syntax.PatternValue.literal.inj (leftShape.symm.trans rightShape)
  subst rightLiteral
  exact leftMeaning.value_unique rightMeaning

theorem WordMatchPatternClassifies.tag_unique
    {pattern : Syntax.Pattern} {left right : Option Core.Word}
    (first : WordMatchPatternClassifies pattern left)
    (second : WordMatchPatternClassifies pattern right) : left = right := by
  induction first generalizing right with
  | @literal pattern word meaning =>
      cases second with
      | literal other => exact congrArg some (meaning.value_unique other)
      | wildcard shape =>
          obtain ⟨literal, literalShape, _⟩ := meaning
          rw [shape] at literalShape
          cases literalShape
      | group _ => obtain ⟨literal, shape, _⟩ := meaning; cases shape
  | wildcard shape =>
      cases second with
      | literal meaning =>
          obtain ⟨literal, literalShape, _⟩ := meaning
          rw [shape] at literalShape
          cases literalShape
      | wildcard _ => rfl
      | group _ => cases shape
  | group _ ih =>
      cases second with
      | literal meaning => obtain ⟨literal, shape, _⟩ := meaning; cases shape
      | wildcard shape => cases shape
      | group other => exact ih other

theorem WordMatchPatternClassifies.value_unique
    {pattern : Syntax.Pattern} {left right : Core.Word}
    (first : WordMatchPatternClassifies pattern (some left))
    (second : WordMatchPatternClassifies pattern (some right)) : left = right :=
  Option.some.inj (first.tag_unique second)

private theorem classified_checks {pattern : Syntax.Pattern} {tag : Option Core.Word}
    (meaning : WordMatchPatternClassifies pattern tag) :
    interpretWordMatchPattern? pattern = some tag := by
  induction meaning with
  | @literal pattern word meaning =>
      obtain ⟨literal, shape, denotes⟩ := meaning
      rcases pattern with ⟨span, value⟩
      change value = .literal literal at shape
      subst value
      simp [interpretWordMatchPattern?, interpretWordLiteral?_iff.mpr denotes]
  | @wildcard pattern marker shape =>
      rcases pattern with ⟨span, value⟩
      change value = .wildcard marker at shape
      subst value
      simp only [interpretWordMatchPattern?]
  | group _ ih => simpa only [interpretWordMatchPattern?] using ih

private theorem checked_classifies (pattern : Syntax.Pattern) (tag : Option Core.Word)
    (checked : interpretWordMatchPattern? pattern = some tag) :
    WordMatchPatternClassifies pattern tag := by
  cases pattern with
  | mk span value =>
      cases value <;> simp only [interpretWordMatchPattern?] at checked
      all_goals try cases checked
      case literal literal =>
        obtain ⟨word, found, rfl⟩ := Option.map_eq_some_iff.mp checked
        exact .literal ⟨literal, rfl, interpretWordLiteral?_iff.mp found⟩
      case wildcard.refl marker => exact .wildcard rfl
      case group inner => exact .group (checked_classifies inner tag checked)
termination_by sizeOf pattern

theorem interpretWordMatchPattern?_iff {pattern : Syntax.Pattern} {tag : Option Core.Word} :
    interpretWordMatchPattern? pattern = some tag ↔ WordMatchPatternClassifies pattern tag :=
  ⟨checked_classifies pattern tag, classified_checks⟩

theorem WordMatchChooses.deterministic
    {value : Core.Value} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {left right : Syntax.Block}
    {leftTests rightTests : Nat}
    (first : WordMatchChooses value cases defaultBody left leftTests)
    (second : WordMatchChooses value cases defaultBody right rightTests) :
    left = right ∧ leftTests = rightTests := by
  induction first generalizing right rightTests with
  | fallback => cases second; exact ⟨rfl, rfl⟩
  | wildcard shape =>
      cases second with
      | wildcard _ => exact ⟨rfl, rfl⟩
      | hit meaning => cases shape.tag_unique meaning
      | miss meaning _ _ => cases shape.tag_unique meaning
  | hit meaning =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit _ => exact ⟨rfl, rfl⟩
      | miss other different _ => exact False.elim (different (meaning.value_unique other))
  | miss meaning different _ ih =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit other => exact False.elim (different (other.value_unique meaning))
      | miss _ _ tail =>
          obtain ⟨rfl, rfl⟩ := ih tail
          exact ⟨rfl, rfl⟩

end Solcore.Frontend
