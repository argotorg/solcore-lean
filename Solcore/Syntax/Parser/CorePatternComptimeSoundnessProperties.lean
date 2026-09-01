import Solcore.Syntax.DeclarativeCorePatternComptimeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Pattern

/-!
Diagnostic reflection and exact parser-independent soundness for the Core
compile-time pattern.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

/-- Compile-time-pattern success reflects diagnostic freedom through the
supplied expression parser. -/
theorem comptimePattern_reflectsDiagnosticFreeOnSuccess
    (expression : Parser Expr)
    (expressionReflects :
      Parser.ReflectsDiagnosticFreeOnSuccess expression) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (comptimePattern expression) := by
  intro input pattern next result diagnosticFree
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok value afterExpression =>
          simp only [expressionResult] at result
          cases result
          have afterMarkerFree := expressionReflects afterMarker value
            next expressionResult diagnosticFree
          exact contextual_reflectsDiagnosticFreeOnSuccess .comptime .pattern
            input marker afterMarker markerResult afterMarkerFree

/-- Every diagnostic-free compile-time-pattern success consumes the exact
contextual marker and follows the supplied expression grammar. -/
theorem comptimePattern_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {pattern : Pattern}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : comptimePattern expression input = .ok pattern next) :
    DeclarativeGrammar.ComptimePatternParses expressionParses
      input.declarativeRemainder pattern next.declarativeRemainder := by
  unfold comptimePattern at result
  cases markerResult : contextual .comptime .pattern input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      simp only [markerResult] at result
      cases expressionResult : expression afterMarker with
      | invariant error => simp [expressionResult] at result
      | reject failure rejected => simp [expressionResult] at result
      | ok value afterExpression =>
          simp only [expressionResult] at result
          cases result
          exact .parsed marker.span
            (contextual_success_exactTokenParses .comptime .pattern
              markerResult)
            (expressionSound diagnosticFree expressionResult)

end Solcore.Syntax.Parser.PatternInternals
