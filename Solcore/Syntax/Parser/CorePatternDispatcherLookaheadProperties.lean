import Solcore.Syntax.DeclarativeCorePatternGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Literal

/-! Executable-to-declarative lookahead bridges for ordered pattern parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- A false Boolean guard excludes both declarative Boolean starters. -/
theorem not_booleanPatternStartsAt_of_isBooleanValue_eq_false
    {input : State} (absent : isBooleanValue input = false) :
    ¬ DeclarativeGrammar.BooleanPatternStartsAt
      input.declarativeRemainder := by
  have parts : isKeyword input .trueKw = false ∧
      isKeyword input .falseKw = false :=
    Bool.or_eq_false_iff.mp (by
      simpa only [isBooleanValue] using absent)
  intro starts
  rcases starts with ⟨span, token⟩ | ⟨span, token⟩
  · exact (keywordAbsentAt_of_isKeyword_eq_false .trueKw parts.1)
      ⟨span, token⟩
  · exact (keywordAbsentAt_of_isKeyword_eq_false .falseKw parts.2)
      ⟨span, token⟩

end Solcore.Syntax.Parser.PatternInternals
