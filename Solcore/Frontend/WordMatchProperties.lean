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

theorem WordMatchChooses.deterministic
    {value : Core.Value} {cases : List Syntax.MatchCase} {defaultBody left right : Syntax.Block}
    {leftTests rightTests : Nat}
    (first : WordMatchChooses value cases defaultBody left leftTests)
    (second : WordMatchChooses value cases defaultBody right rightTests) :
    left = right ∧ leftTests = rightTests := by
  induction first generalizing right rightTests with
  | fallback => cases second; exact ⟨rfl, rfl⟩
  | hit meaning =>
      cases second with
      | hit _ => exact ⟨rfl, rfl⟩
      | miss other different _ => exact False.elim (different (meaning.value_unique other))
  | miss meaning different _ ih =>
      cases second with
      | hit other => exact False.elim (different (other.value_unique meaning))
      | miss _ _ tail =>
          obtain ⟨rfl, rfl⟩ := ih tail
          exact ⟨rfl, rfl⟩

end Solcore.Frontend
