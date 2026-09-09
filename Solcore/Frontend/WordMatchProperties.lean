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

private theorem literal_not_wildcard {pattern : Syntax.Pattern} {word : Core.Word}
    {marker : Syntax.SourceSpan} (meaning : WordMatchPatternDenotes pattern word)
    (shape : pattern.value = .wildcard marker) : False := by
  obtain ⟨literal, literalShape, _⟩ := meaning
  rw [shape] at literalShape
  cases literalShape

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
      | hit meaning => exact False.elim (literal_not_wildcard meaning shape)
      | miss meaning _ _ => exact False.elim (literal_not_wildcard meaning shape)
  | hit meaning =>
      cases second with
      | wildcard shape => exact False.elim (literal_not_wildcard meaning shape)
      | hit _ => exact ⟨rfl, rfl⟩
      | miss other different _ => exact False.elim (different (meaning.value_unique other))
  | miss meaning different _ ih =>
      cases second with
      | wildcard shape => exact False.elim (literal_not_wildcard meaning shape)
      | hit other => exact False.elim (different (other.value_unique meaning))
      | miss _ _ tail =>
          obtain ⟨rfl, rfl⟩ := ih tail
          exact ⟨rfl, rfl⟩

end Solcore.Frontend
