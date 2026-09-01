import Solcore.Syntax.DeclarativeCoreStatementSimpleGrammar
import Solcore.Syntax.Parser.CoreStatementSimpleDiagnosticReflectionProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-!
Exact parser-independent soundness for Core `let` and `return` statements.
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

private theorem symbolTokenAt_of_isSymbol_eq_true (symbolValue : Symbol)
    {input : State} (present : isSymbol input symbolValue = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol symbolValue } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol symbolValue) = true at present
      have parsed : symbol symbolValue .statement input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span,
        (symbol_ok_tokenAt symbolValue .statement parsed).1⟩

namespace StatementSimpleInternals

theorem optionalSemicolon_success_sound {input next : State}
    {value : Option SourceSpan}
    (result : optionalSemicolon input = .ok value next) :
    DeclarativeGrammar.OptionalStatementSemicolonParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold optionalSemicolon getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon
  · simp only [present, if_true] at result
    cases semicolonResult : symbol .semicolon .statement input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok semicolon afterSemicolon =>
        simp only [semicolonResult, pure] at result
        cases result
        exact .present semicolon.span
          (symbol_success_exactTokenParses .semicolon .statement
            semicolonResult)
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)

theorem optionalReturnValue_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Option Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalReturnValue expression input = .ok value next) :
    DeclarativeGrammar.OptionalReturnValueParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon
  · simp only [present, if_true, pure] at result
    cases result
    rcases symbolTokenAt_of_isSymbol_eq_true .semicolon present with
      ⟨span, token⟩
    exact .absent span token
  · have absent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false] at result
    rcases bind_ok_components result with
      ⟨expressionValue, afterExpression, expressionResult, finished⟩
    cases finished
    exact .present (symbolAbsentAt_of_isSymbol_eq_false .semicolon absent)
      (expressionSound diagnosticFree expressionResult)

theorem optionalLetType_success_sound {input next : State}
    {value : Option TypeExpr}
    (result : optionalLetType input = .ok value next) :
    DeclarativeGrammar.OptionalLetTypeParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold optionalLetType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .colon
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components rest with
      ⟨type, afterType, typeResult, finished⟩
    cases finished
    exact .present colon.span
      (symbol_success_exactTokenParses .colon .statement colonResult)
      (typeExpr_success_sound typeResult)
  · have absent : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .colon absent)

theorem optionalLetInitializer_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Option Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : optionalLetInitializer expression input = .ok value next) :
    DeclarativeGrammar.OptionalLetInitializerParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold optionalLetInitializer getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .equal
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨equal, afterEqual, equalResult, rest⟩
    rcases bind_ok_components rest with
      ⟨expressionValue, afterExpression, expressionResult, finished⟩
    cases finished
    exact .present equal.span
      (symbol_success_exactTokenParses .equal .statement equalResult)
      (expressionSound diagnosticFree expressionResult)
  · have absent : isSymbol input .equal = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .equal absent)

end StatementSimpleInternals

theorem letStatement_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : letStatement expression input = .ok value next) :
    DeclarativeGrammar.LetStatementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold letStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, typeStage⟩
  rcases bind_ok_components typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have afterInitializerFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .statement afterInitializer semicolon next semicolonResult
      diagnosticFree
  exact .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .letKw .statement markerResult)
    (identifier_success_sound .statement nameResult)
    (StatementSimpleInternals.optionalLetType_success_sound typeResult)
    (StatementSimpleInternals.optionalLetInitializer_success_sound expression
      expressionParses expressionSound afterInitializerFree initializerResult)
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult)

theorem returnStatement_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Statement}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : returnStatement expression input = .ok value next) :
    DeclarativeGrammar.ReturnStatementParses expressionParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold returnStatement at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, valueStage⟩
  rcases bind_ok_components valueStage with
    ⟨returnValue, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have afterValueFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .statement afterValue semicolon next semicolonResult
      diagnosticFree
  exact .parsed marker.span semicolon.span
    (keyword_success_exactTokenParses .returnKw .statement markerResult)
    (StatementSimpleInternals.optionalReturnValue_success_sound expression
      expressionParses expressionSound afterValueFree valueResult)
    (symbol_success_exactTokenParses .semicolon .statement semicolonResult)

end Solcore.Syntax.Parser
