import Solcore.Syntax.DeclarativeCoreForStatementGrammar
import Solcore.Syntax.Parser.CoreAssignmentTailSoundnessProperties
import Solcore.Syntax.Parser.CoreForItemDiagnosticReflectionProperties
import Solcore.Syntax.Parser.CoreStatementSimpleSoundnessProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Statement.ForItemFuelTotalityProperties

/-!
Exact diagnostic-free soundness and strict progress for Core `for` header
items.
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

namespace StatementSimpleInternals

@[simp] theorem forLetEnd_eq_declarative (name : Identifier)
    (type : Option TypeExpr) (initializer : Option Expr) :
    forLetEnd name type initializer =
      DeclarativeGrammar.forLetEnd name type initializer := by
  rfl

theorem forLetItem_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {item : ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forLetItem expression input = .ok item next) :
    DeclarativeGrammar.ForLetItemParses expressionParses
      input.declarativeRemainder item next.declarativeRemainder := by
  unfold forLetItem at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, typeStage⟩
  rcases bind_ok_components typeStage with
    ⟨type, afterType, typeResult, initializerStage⟩
  rcases bind_ok_components initializerStage with
    ⟨initializer, afterInitializer, initializerResult, finished⟩
  cases finished
  exact .parsed marker.span
    (keyword_success_exactTokenParses .letKw .statement markerResult)
    (identifier_success_sound .statement nameResult)
    (optionalLetType_success_sound typeResult)
    (optionalLetInitializer_success_sound expression expressionParses
      expressionSound diagnosticFree initializerResult)

theorem forAssignmentOrExpression_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {item : ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forAssignmentOrExpression expression input = .ok item next) :
    DeclarativeGrammar.ForAssignmentOrExpressionParses expressionParses
      input.declarativeRemainder item next.declarativeRemainder := by
  unfold forAssignmentOrExpression at result
  rcases bind_ok_components result with
    ⟨left, afterLeft, leftResult, tailStage⟩
  rcases bind_ok_components tailStage with
    ⟨tail, afterTail, tailResult, finished⟩
  have afterTailFree : afterTail.diagnosticsRev = [] := by
    cases tail with
    | none => cases finished; exact diagnosticFree
    | some tail =>
        cases tail <;> cases finished <;> exact diagnosticFree
  have afterLeftFree :=
    optionalAssignmentTail_reflectsDiagnosticFreeOnSuccess expression
      expressionReflects afterLeft tail afterTail tailResult afterTailFree
  have leftGrammar := expressionSound afterLeftFree leftResult
  have tailGrammar := optionalAssignmentTail_success_sound expression
    expressionParses expressionSound afterTailFree tailResult
  cases tail with
  | none =>
      cases finished
      exact ⟨left, afterLeft.declarativeRemainder, none, leftGrammar,
        tailGrammar, .expression left⟩
  | some tail =>
      cases tail with
      | value operator right =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.value operator right), leftGrammar, tailGrammar,
            .value left right operator⟩
      | bitNot operator =>
          cases finished
          exact ⟨left, afterLeft.declarativeRemainder,
            some (.bitNot operator), leftGrammar, tailGrammar,
            .bitNot left operator⟩

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem forItem_success_sound
    (expression : Parser Expr)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {item : ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forItem expression input = .ok item next) :
    DeclarativeGrammar.ForItemParses expressionParses
      input.declarativeRemainder item next.declarativeRemainder := by
  unfold forItem at result
  by_cases letPresent : isKeyword input .letKw
  · simp only [letPresent, if_true] at result
    exact .letItem
      (StatementSimpleInternals.forLetItem_success_sound expression
        expressionParses expressionSound diagnosticFree result)
  · have letAbsent : isKeyword input .letKw = false :=
      Bool.eq_false_iff.mpr letPresent
    simp only [letAbsent, Bool.false_eq_true, if_false] at result
    exact .assignmentOrExpression
      (keywordAbsentAt_of_isKeyword_eq_false .letKw letAbsent)
      (StatementSimpleInternals.forAssignmentOrExpression_success_sound
        expression expressionParses expressionReflects expressionSound
          diagnosticFree result)

/-- A successful public item advances whenever the expression parser does. -/
theorem forItem_cursor_lt_onSuccess_of_expressionStrict
    (expression : Parser Expr)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input next : State} {item : ForItem}
    (result : forItem expression input = .ok item next) :
    input.cursor < next.cursor := by
  unfold forItem at result
  split at result
  · exact StatementSimpleInternals.forLetItem_cursor_lt_onSuccess
      expression (fun _ _ _ parsed => Nat.le_of_lt (expressionStrict parsed))
        result
  · exact
      StatementSimpleInternals.forAssignmentOrExpression_cursor_lt_onSuccess
        expression expressionStrict result

end Solcore.Syntax.Parser
