import Solcore.Syntax.Parser.CoreBlockSoundnessProperties
import Solcore.Syntax.Parser.CoreForItemsSoundnessProperties

/-!
Exact diagnostic-free soundness for complete canonical Core `for`
statements.
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

theorem forStatement_success_sound
    (statement : Parser Statement) (expression : Parser Expr)
    (statementParses : DeclarativeGrammar.Remainder → Statement →
      DeclarativeGrammar.Remainder → Prop)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (statementReflects : Parser.ReflectsDiagnosticFreeOnSuccess statement)
    (statementSound : ∀ {input next : State} {value : Statement},
      next.diagnosticsRev = [] → statement input = .ok value next →
      statementParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forStatement statement expression input = .ok value next) :
    DeclarativeGrammar.ForStatementParses statementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold forStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, openingStage⟩
  rcases bind_ok_components openingStage with
    ⟨opening, afterOpening, openingResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult,
      firstSemicolonStage⟩
  rcases bind_ok_components firstSemicolonStage with
    ⟨firstSemicolon, afterFirstSemicolon, firstSemicolonResult,
      conditionStage⟩
  rcases bind_ok_components conditionStage with
    ⟨condition, afterCondition, conditionResult, secondSemicolonStage⟩
  rcases bind_ok_components secondSemicolonStage with
    ⟨secondSemicolon, afterSecondSemicolon, secondSemicolonResult,
      postStage⟩
  rcases bind_ok_components postStage with
    ⟨post, afterPost, postResult, closingStage⟩
  rcases bind_ok_components closingStage with
    ⟨closing, afterClosing, closingResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterClosingFree := coreBlock_reflectsDiagnosticFreeOnSuccess
    statement .require statementReflects afterClosing body next
      bodyResult diagnosticFree
  have afterPostFree := symbol_reflectsDiagnosticFreeOnSuccess .rightParen
    .statement afterPost closing afterClosing closingResult afterClosingFree
  have afterSecondSemicolonFree :=
    ControlInternals.forItems_reflectsDiagnosticFreeOnSuccess expression
      .rightParen expressionReflects afterSecondSemicolon post afterPost
        postResult afterPostFree
  have afterConditionFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .statement afterCondition secondSemicolon
      afterSecondSemicolon secondSemicolonResult afterSecondSemicolonFree
  have afterFirstSemicolonFree := expressionReflects afterFirstSemicolon
    condition afterCondition conditionResult afterConditionFree
  have afterInitializerFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .statement afterInitializer firstSemicolon
      afterFirstSemicolon firstSemicolonResult afterFirstSemicolonFree
  exact .parsed marker.span opening.span firstSemicolon.span
    secondSemicolon.span closing.span
    (keyword_success_exactTokenParses .forKw .statement markerResult)
    (symbol_success_exactTokenParses .leftParen .statement openingResult)
    (ControlInternals.forItems_success_sound expression .semicolon
      expressionParses expressionReflects expressionSound expressionStrict
        afterInitializerFree initializerResult)
    (symbol_success_exactTokenParses .semicolon .statement
      firstSemicolonResult)
    (expressionSound afterConditionFree conditionResult)
    (symbol_success_exactTokenParses .semicolon .statement
      secondSemicolonResult)
    (ControlInternals.forItems_success_sound expression .rightParen
      expressionParses expressionReflects expressionSound expressionStrict
        afterPostFree postResult)
    (symbol_success_exactTokenParses .rightParen .statement closingResult)
    (coreBlock_success_sound statementParses statement .require
      statementReflects statementSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser
