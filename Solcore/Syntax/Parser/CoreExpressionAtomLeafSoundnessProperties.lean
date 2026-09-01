import Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
import Solcore.Syntax.Parser.CoreLiteralSoundnessProperties
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-!
Diagnostic reflection and declarative soundness for Core expression leaves.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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

namespace ExpressionAtomInternals

/-- Literal-expression success never removes an earlier diagnostic. -/
theorem literalExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess literalExpression := by
  unfold literalExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    coreLiteral_reflectsDiagnosticFreeOnSuccess
  intro literal
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Identifier-expression success never removes an earlier diagnostic. -/
theorem identifierExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess identifierExpression := by
  unfold identifierExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    expressionName_reflectsDiagnosticFreeOnSuccess
  intro name
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Proxy-expression success reflects through its marker and nested type. -/
theorem proxyExpression_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess proxyExpression := by
  unfold proxyExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .at .expression)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    typeExpr_reflectsDiagnosticFreeOnSuccess
  intro type
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every successful literal expression follows its exact leaf grammar. -/
theorem literalExpression_success_sound {input next : State}
    {expression : Expr}
    (result : literalExpression input = .ok expression next) :
    DeclarativeGrammar.LiteralExpressionParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold literalExpression at result
  rcases bind_ok_components result with
    ⟨literal, afterLiteral, literalResult, finished⟩
  cases finished
  exact .parsed (coreLiteral_success_sound literalResult)

/-- Every successful identifier expression follows its exact leaf grammar. -/
theorem identifierExpression_success_sound {input next : State}
    {expression : Expr}
    (result : identifierExpression input = .ok expression next) :
    DeclarativeGrammar.IdentifierExpressionParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold identifierExpression at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, finished⟩
  cases finished
  exact .parsed (expressionName_success_sound nameResult)

/-- Every successful proxy expression follows its exact leaf grammar. -/
theorem proxyExpression_success_sound {input next : State}
    {expression : Expr}
    (result : proxyExpression input = .ok expression next) :
    DeclarativeGrammar.ProxyExpressionParses
      input.declarativeRemainder expression next.declarativeRemainder := by
  unfold proxyExpression at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨type, afterType, typeResult, finished⟩
  cases finished
  exact .parsed marker.span
    (symbol_success_exactTokenParses .at .expression markerResult)
    (typeExpr_success_sound typeResult)

/-- Literal leaf soundness composes with source provenance. -/
theorem literalExpression_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    {input next : State} {expression : Expr} (inputValid : input.ValidFor)
    (result : literalExpression input = .ok expression next) :
    DeclarativeGrammar.LiteralExpressionParses
        input.declarativeRemainder expression next.declarativeRemainder ∧
      Expr.ValidFor statementValid input.file expression := by
  refine ⟨literalExpression_success_sound result, ?_⟩
  have valid := literalExpression_validFor statementValid input inputValid
  rw [result] at valid
  exact valid.1

/-- Identifier leaf soundness composes with source provenance. -/
theorem identifierExpression_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    {input next : State} {expression : Expr} (inputValid : input.ValidFor)
    (result : identifierExpression input = .ok expression next) :
    DeclarativeGrammar.IdentifierExpressionParses
        input.declarativeRemainder expression next.declarativeRemainder ∧
      Expr.ValidFor statementValid input.file expression := by
  refine ⟨identifierExpression_success_sound result, ?_⟩
  have valid := identifierExpression_validFor statementValid input inputValid
  rw [result] at valid
  exact valid.1

/-- Proxy leaf soundness composes with source provenance. -/
theorem proxyExpression_success_sound_and_validFor
    (statementValid : SourceFile → Statement → Prop)
    {input next : State} {expression : Expr} (inputValid : input.ValidFor)
    (result : proxyExpression input = .ok expression next) :
    DeclarativeGrammar.ProxyExpressionParses
        input.declarativeRemainder expression next.declarativeRemainder ∧
      Expr.ValidFor statementValid input.file expression := by
  refine ⟨proxyExpression_success_sound result, ?_⟩
  have valid := proxyExpression_validFor statementValid input inputValid
  rw [result] at valid
  exact valid.1

end ExpressionAtomInternals

end Solcore.Syntax.Parser
