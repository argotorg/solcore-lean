import Solcore.Syntax.Parser.YulExpressionLayerSoundnessProperties
import Solcore.Syntax.Parser.YulNamesDiagnosticReflectionProperties
import Solcore.Syntax.Parser.Yul.Statement

/-!
Diagnostic reflection for the public inline-Yul expression parser and the
basic statement forms built from it.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulExpressionInternals

/-- Every fuel-bounded public expression parser reflects diagnostic freedom. -/
theorem withFuel_reflectsDiagnosticFreeOnSuccess : ∀ fuel,
    Parser.ReflectsDiagnosticFreeOnSuccess (withFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input expression next result diagnosticFree
      simp [withFuel] at result
  | succ fuel inductionHypothesis =>
      exact yulExpressionLayer_reflectsDiagnosticFreeOnSuccess
        (withFuel fuel) inductionHypothesis

end YulExpressionInternals

/-- The fixed public inline-Yul expression parser cannot erase diagnostics. -/
theorem yulExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulExpression := by
  intro input expression next result diagnosticFree
  unfold yulExpression at result
  exact YulExpressionInternals.withFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input expression next result diagnosticFree

/-- Optional Yul `let` initialization reflects through its committed branch. -/
theorem yulLetInitializer_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .colonEqual .yulStatement)
    intro operator
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      yulExpression_reflectsDiagnosticFreeOnSuccess
    intro value
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Inline-Yul `let` parsing reflects through names and initialization. -/
theorem yulLetStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .letKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulNames_reflectsDiagnosticFreeOnSuccess
  intro names
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulLetInitializer_reflectsDiagnosticFreeOnSuccess
  intro initializer
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Inline-Yul assignment parsing reflects through targets and value. -/
theorem yulAssignment_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulNames_reflectsDiagnosticFreeOnSuccess
  intro names
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .colonEqual .yulStatement)
  intro operator
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro value
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Inline-Yul expression statements reflect through their expression. -/
theorem yulExpressionStatement_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    yulExpression_reflectsDiagnosticFreeOnSuccess
  intro expression
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Source-level Yul `return(...)` reflects through its argument list. -/
theorem yulReturnBuiltin_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .returnKw .yulStatement)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      yulExpression .yulExpression .yul
        yulExpression_reflectsDiagnosticFreeOnSuccess)
  intro arguments
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
