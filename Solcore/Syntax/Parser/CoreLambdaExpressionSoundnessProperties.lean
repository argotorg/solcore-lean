import Solcore.Syntax.Parser.CoreLambdaParameterSoundnessProperties
import Solcore.Syntax.Parser.CoreLambdaReturnTypeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedAllowEmptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.ParameterProperties

/-!
Diagnostic reflection and exact parser-independent soundness for Core lambda
expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- A diagnostic-free successful lambda parse had a diagnostic-free input
whenever its supplied block parser has the same property. -/
theorem lambdaExpression_reflectsDiagnosticFreeOnSuccess
    (block : Parser Block)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess (lambdaExpression block) := by
  unfold lambdaExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .lamKw .expression)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      lambdaParameter .parameter .expression
      lambdaParameter_reflectsDiagnosticFreeOnSuccess)
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalLambdaReturnType_reflectsDiagnosticFreeOnSuccess
  intro returnType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess blockReflects
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free successful lambda parse follows the exact
parser-independent lambda grammar over the supplied block judgment. -/
theorem lambdaExpression_success_sound
    (block : Parser Block)
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block)
    (blockSound : ∀ {input next : State} {value : Block},
      next.diagnosticsRev = [] → block input = .ok value next →
      blockParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : lambdaExpression block input = .ok value next) :
    DeclarativeGrammar.LambdaExpressionParses blockParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold lambdaExpression at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, parametersStage⟩
  rcases bind_ok_components parametersStage with
    ⟨parameters, afterParameters, parametersResult, returnStage⟩
  rcases bind_ok_components returnStage with
    ⟨returnType, afterReturn, returnResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterReturnFree := blockReflects afterReturn body next bodyResult
    diagnosticFree
  have afterParametersFree :=
    optionalLambdaReturnType_reflectsDiagnosticFreeOnSuccess
      afterParameters returnType afterReturn returnResult afterReturnFree
  have parametersGrammar :=
    delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
      .leftParen .rightParen lambdaParameter
      DeclarativeGrammar.LambdaParameterParses .parameter .expression
      lambdaParameter_success_sound
      lambdaParameter_reflectsDiagnosticFreeOnSuccess
      lambdaParameter_preservesTokenWindow afterParametersFree
      parametersResult
  exact .parsed marker.span
    (keyword_success_exactTokenParses .lamKw .expression markerResult)
    parametersGrammar
    (optionalLambdaReturnType_success_sound returnResult)
    (blockSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
