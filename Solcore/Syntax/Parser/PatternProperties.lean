import Solcore.Syntax.Parser.Pattern
import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.PatternValidity

/-! Provenance and carrier contracts for canonical pattern parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace PatternInternals

/-- Wildcard parsing retains both the outer and marker source ranges. -/
theorem wildcardPattern_validFor
    (expressionValid : SourceFile → Expr → Prop) :
    wildcardPattern.ValidFor (Pattern.ValidFor expressionValid) := by
  unfold wildcardPattern
  apply Parser.bind_validFor_of_value
    (symbol_validFor .underscore .pattern)
  intro marker input inputValid markerValid
  exact ⟨Pattern.ValidFor.wildcard markerValid markerValid,
    inputValid, rfl⟩

/-- Wildcard parsing preserves every ordinary token window. -/
theorem wildcardPattern_preservesTokenWindow :
    Parser.PreservesTokenWindow wildcardPattern := by
  unfold wildcardPattern
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .underscore .pattern)
  intro marker
  exact Parser.pure_preservesTokenWindow _

theorem wildcardPattern_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess wildcardPattern :=
  wildcardPattern_preservesTokenWindow.preservesTokensOnSuccess

/-- Wildcard parsing advances without rewinding the cursor. -/
theorem wildcardPattern_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess wildcardPattern := by
  unfold wildcardPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .underscore .pattern)
  intro marker
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A wildcard pattern starts at its underscore token. -/
theorem wildcardPattern_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess wildcardPattern (·.span) := by
  unfold wildcardPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .underscore .pattern)
  intro marker input value final parsed
  cases parsed
  rfl

/-- Literal-pattern parsing retains both equal literal ranges. -/
theorem literalPattern_validFor
    (expressionValid : SourceFile → Expr → Prop) :
    literalPattern.ValidFor (Pattern.ValidFor expressionValid) := by
  unfold literalPattern
  apply Parser.bind_validFor_of_value coreLiteral_validFor
  intro literal input inputValid literalValid
  exact ⟨Pattern.ValidFor.literal literalValid literalValid,
    inputValid, rfl⟩

/-- Literal patterns preserve every ordinary token window. -/
theorem literalPattern_preservesTokenWindow :
    Parser.PreservesTokenWindow literalPattern := by
  unfold literalPattern
  apply Parser.bind_preservesTokenWindow coreLiteral_preservesTokenWindow
  intro literal
  exact Parser.pure_preservesTokenWindow _

theorem literalPattern_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess literalPattern :=
  literalPattern_preservesTokenWindow.preservesTokensOnSuccess

/-- Literal-pattern parsing never rewinds the cursor. -/
theorem literalPattern_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess literalPattern := by
  unfold literalPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    coreLiteral_cursorMonotoneOnSuccess
  intro literal
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A literal pattern starts at its literal token. -/
theorem literalPattern_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess literalPattern (·.span) := by
  unfold literalPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    coreLiteral_startsAtCurrentTokenOnSuccess
  intro literal input value final parsed
  cases parsed
  rfl

/-- Boolean binder patterns retain both equal builtin-name ranges. -/
theorem booleanBinderPattern_validFor
    (expressionValid : SourceFile → Expr → Prop) :
    booleanBinderPattern.ValidFor (Pattern.ValidFor expressionValid) := by
  unfold booleanBinderPattern
  apply Parser.bind_validFor_of_value booleanIdentifier_validFor
  intro name input inputValid nameValid
  exact ⟨Pattern.ValidFor.binder nameValid nameValid, inputValid, rfl⟩

/-- Boolean binder patterns preserve every ordinary token window. -/
theorem booleanBinderPattern_preservesTokenWindow :
    Parser.PreservesTokenWindow booleanBinderPattern := by
  unfold booleanBinderPattern
  apply Parser.bind_preservesTokenWindow
    booleanIdentifier_preservesTokenWindow
  intro name
  exact Parser.pure_preservesTokenWindow _

theorem booleanBinderPattern_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess booleanBinderPattern :=
  booleanBinderPattern_preservesTokenWindow.preservesTokensOnSuccess

/-- Boolean binder parsing never rewinds the cursor. -/
theorem booleanBinderPattern_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess booleanBinderPattern := by
  unfold booleanBinderPattern
  apply Parser.bind_cursorMonotoneOnSuccess
    booleanIdentifier_cursorMonotoneOnSuccess
  intro name
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A Boolean binder pattern starts at its keyword token. -/
theorem booleanBinderPattern_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess booleanBinderPattern (·.span) := by
  unfold booleanBinderPattern
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    booleanIdentifier_startsAtCurrentTokenOnSuccess
  intro name input value final parsed
  cases parsed
  rfl

end PatternInternals
end Solcore.Syntax.Parser
