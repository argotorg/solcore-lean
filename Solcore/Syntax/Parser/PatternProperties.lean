import Solcore.Syntax.Parser.Pattern
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

end PatternInternals
end Solcore.Syntax.Parser
