import Solcore.Syntax.Parser.Statement.SimpleBranchFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.ControlProperties

/-! Fuel-aware totality for one canonical Core `for`-header item. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

private theorem bind_cursor_lt_of_first {α β : Type}
    {first : Parser α} {next : α → Parser β}
    (firstStrict : ∀ {input middle : State} {value : α},
      first input = .ok value middle → input.cursor < middle.cursor)
    (nextMonotone : ∀ value, Parser.CursorMonotoneOnSuccess (next value))
    {input final : State} {value : β}
    (parsed : (first >>= next) input = .ok value final) :
    input.cursor < final.cursor := by
  cases firstResult : first input with
  | ok firstValue middle =>
      simp only [bind, firstResult] at parsed
      exact Nat.lt_of_lt_of_le (firstStrict firstResult)
        (nextMonotone firstValue middle value final parsed)
  | reject failure rejected => simp [bind, firstResult] at parsed
  | invariant error => simp [bind, firstResult] at parsed

theorem forLetItem_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ item next, forLetItem expression input = .ok item next) ∨
    (∃ failure next,
      forLetItem expression input = .reject failure next) := by
  rcases (keyword_ordinary .letKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .letKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .letKw .statement input
    rw [markerResult] at markerWindow
    have afterMarkerAdequate :
        afterMarker.remainingCount < expressionFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .letKw) .statement
          (· == .keyword .letKw) markerResult) adequate
    rcases (identifier_ordinary .statement) afterMarker with
      ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · have nameReply := identifier_validFor .statement afterMarker
        markerReply.2.1
      rw [nameResult] at nameReply
      have nameWindow := identifier_preservesTokenWindow .statement afterMarker
      rw [nameResult] at nameWindow
      have afterNameAdequate : afterName.remainingCount < expressionFuel :=
        remainingCount_lt_of_cursor_le nameWindow.2
          (identifier_cursorMonotoneOnSuccess .statement afterMarker name
            afterName nameResult) afterMarkerAdequate
      rcases optionalLetType_invariantFreeOnValid afterName nameReply.2.1 with
        ⟨type, afterType, typeResult⟩ | ⟨failure, rejected, typeResult⟩
      · have typeReply := optionalLetType_validFor afterName nameReply.2.1
        rw [typeResult] at typeReply
        have typeWindow := optionalLetType_preservesTokenWindow afterName
        rw [typeResult] at typeWindow
        have afterTypeAdequate :
            afterType.remainingCount < expressionFuel :=
          remainingCount_lt_of_cursor_le typeWindow.2
            (optionalLetType_cursorMonotoneOnSuccess afterName type afterType
              typeResult) afterNameAdequate
        rcases optionalLetInitializer_ordinary_of_expressionFuel expression
            expressionFuel contract afterType typeReply.2.1 afterTypeAdequate
          with ⟨initializer, final, initializerResult⟩ |
            ⟨failure, rejected, initializerResult⟩
        · let endSpan := forLetEnd name type initializer
          exact Or.inl ⟨{
              span := SourceSpan.cover marker.span endSpan
              value := .letDecl name type initializer
            }, final, by
              simp only [forLetItem, bind, markerResult, nameResult,
                typeResult, initializerResult, pure, endSpan]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [forLetItem, bind, markerResult, nameResult,
              typeResult, initializerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [forLetItem, bind, markerResult, nameResult, typeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [forLetItem, bind, markerResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [forLetItem, bind, markerResult]⟩

theorem forAssignmentOrExpression_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ item next,
      forAssignmentOrExpression expression input = .ok item next) ∨
    (∃ failure next,
      forAssignmentOrExpression expression input = .reject failure next) := by
  rcases contract.ordinary input inputValid adequate with
    ⟨left, afterLeft, leftResult⟩ | ⟨failure, rejected, leftResult⟩
  · have leftReply := contract.validFor input inputValid
    rw [leftResult] at leftReply
    have leftWindow := contract.preservesTokenWindow input
    rw [leftResult] at leftWindow
    have tailAdequate : afterLeft.remainingCount < expressionFuel :=
      remainingCount_lt_of_cursor_le leftWindow.2
        (Nat.le_of_lt (contract.cursorLtOnSuccess leftResult)) adequate
    rcases optionalAssignmentTail_ordinary_of_expressionFuel expression
        expressionFuel contract afterLeft leftReply.2.1 tailAdequate with
      ⟨tail, final, tailResult⟩ | ⟨failure, rejected, tailResult⟩
    · cases tail with
      | none =>
          exact Or.inl ⟨{ span := left.span, value := .expression left },
            final, by
              simp only [forAssignmentOrExpression, bind, leftResult,
                tailResult, pure]⟩
      | some tail =>
          cases tail with
          | value operator right =>
              exact Or.inl ⟨{
                  span := SourceSpan.cover left.span right.span
                  value := .assignValue left operator right
                }, final, by
                  simp only [forAssignmentOrExpression, bind, leftResult,
                    tailResult, pure]⟩
          | bitNot operator =>
              exact Or.inl ⟨{
                  span := SourceSpan.cover left.span operator
                  value := .assignBitNot left operator
                }, final, by
                  simp only [forAssignmentOrExpression, bind, leftResult,
                    tailResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [forAssignmentOrExpression, bind, leftResult, tailResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [forAssignmentOrExpression, bind, leftResult]⟩

theorem forLetItem_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionCursor : Parser.CursorMonotoneOnSuccess expression)
    {input final : State} {value : ForItem}
    (parsed : forLetItem expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forLetItem at parsed
  apply bind_cursor_lt_of_first
    (fun result => acceptToken_cursor_lt_onSuccess (.keyword .letKw)
      .statement (· == .keyword .letKw) result) (parsed := parsed)
  intro marker
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .statement)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalLetType_cursorMonotoneOnSuccess
  intro type
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalLetInitializer_cursorMonotoneOnSuccess expression
      expressionCursor)
  intro initializer
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem forAssignmentOrExpression_cursor_lt_onSuccess
    (expression : Parser Expr)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input final : State} {value : ForItem}
    (parsed : forAssignmentOrExpression expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forAssignmentOrExpression at parsed
  apply bind_cursor_lt_of_first expressionStrict (parsed := parsed)
  intro left
  apply Parser.bind_cursorMonotoneOnSuccess
    (optionalAssignmentTail_cursorMonotoneOnSuccess expression
      (fun _ _ _ result => Nat.le_of_lt (expressionStrict result)))
  intro tail
  cases tail with
  | none => exact Parser.pure_cursorMonotoneOnSuccess _
  | some tail =>
      cases tail <;> exact Parser.pure_cursorMonotoneOnSuccess _

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem forItem_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ item next, forItem expression input = .ok item next) ∨
    (∃ failure next, forItem expression input = .reject failure next) := by
  unfold forItem
  split
  · exact StatementSimpleInternals.forLetItem_ordinary_of_expressionFuel
      expression expressionFuel contract input inputValid (by omega)
  · exact
      StatementSimpleInternals.forAssignmentOrExpression_ordinary_of_expressionFuel
        expression expressionFuel contract input inputValid adequate

theorem forItem_cursor_lt_onSuccess
    {statementValid : SourceFile → Statement → Prop}
    (expression : Parser Expr)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    {input final : State} {value : ForItem}
    (parsed : forItem expression input = .ok value final) :
    input.cursor < final.cursor := by
  unfold forItem at parsed
  split at parsed
  · exact StatementSimpleInternals.forLetItem_cursor_lt_onSuccess expression
      expressionSyntax.cursorMonotoneOnSuccess parsed
  · exact
      StatementSimpleInternals.forAssignmentOrExpression_cursor_lt_onSuccess
        expression expressionSyntax.cursorLtOnSuccess parsed

theorem forItem_fuelElementTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (totality : FuelElementTotalityContract expression expressionFuel) :
    FuelElementTotalityContract (forItem expression) expressionFuel := {
  validFor := (forItem_validFor expression (Expr.ValidFor statementValid)
    expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
      expressionSyntax.preservesTokenWindow expressionSyntax.cursorLtOnSuccess
        expressionSyntax.startsAtCurrentTokenOnSuccess).mono
          (fun _ _ _ => trivial)
  preservesTokenWindow := forItem_preservesTokenWindow expression
    expressionSyntax.preservesTokenWindow
  cursorLtOnSuccess := forItem_cursor_lt_onSuccess expression expressionSyntax
  ordinary := forItem_ordinary_of_expressionFuel expression expressionFuel
    totality
}

end Solcore.Syntax.Parser
