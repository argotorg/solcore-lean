import Solcore.Syntax.Parser.Statement.ControlBlockFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.ForItemsFuelTotalityProperties

/-! Fuel-aware totality for complete Core `for` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
All `for` header components remain ordinary below their fixed expression
fuel. Six guaranteed strict prefix steps reach the recursive body.
-/
theorem forStatement_ordinary_of_fuels
    {itemValid : SourceFile → ForItem → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (initializerContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .semicolon)
        expressionFuel)
    (postContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .rightParen)
        expressionFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 7)) :
    (∃ value next,
      forStatement statement expression input = .ok value next) ∨
    (∃ failure next,
      forStatement statement expression input = .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (expressionFuel + 2) (statementFuel + 7))
  have statementBudget : input.remainingCount < statementFuel + 7 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (expressionFuel + 2) (statementFuel + 7))
  rcases (keyword_ordinary .forKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .forKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .forKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .forKw) .statement
        (· == .keyword .forKw) markerResult
    have expressionAfterMarker :
        afterMarker.remainingCount < expressionFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 6 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    rcases (symbol_ordinary .leftParen .statement) afterMarker with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingReply := symbol_validFor .leftParen .statement afterMarker
        markerReply.2.1
      rw [openingResult] at openingReply
      have openingWindow :=
        symbol_preservesTokenWindow .leftParen .statement afterMarker
      rw [openingResult] at openingWindow
      have openingProgress : afterMarker.cursor < afterOpening.cursor :=
        acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .statement
          (· == .symbol .leftParen) openingResult
      have expressionAfterOpening :
          afterOpening.remainingCount < expressionFuel :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      have statementAfterOpening :
          afterOpening.remainingCount < statementFuel + 5 :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      rcases initializerContract.ordinary afterOpening openingReply.2.1
          expressionAfterOpening with
        ⟨initializer, afterInitializer, initializerResult⟩ |
        ⟨failure, rejected, initializerResult⟩
      · have initializerReply := initializerContract.validFor afterOpening
          openingReply.2.1
        rw [initializerResult] at initializerReply
        have initializerWindow := initializerContract.preservesTokenWindow
          afterOpening
        rw [initializerResult] at initializerWindow
        have initializerCursor := initializerContract.cursorMonotoneOnSuccess
          afterOpening initializer afterInitializer initializerResult
        have expressionAfterInitializer :
            afterInitializer.remainingCount < expressionFuel :=
          remainingCount_lt_of_cursor_le initializerWindow.2
            initializerCursor expressionAfterOpening
        have statementAfterInitializer :
            afterInitializer.remainingCount < statementFuel + 5 :=
          remainingCount_lt_of_cursor_le initializerWindow.2
            initializerCursor statementAfterOpening
        rcases (symbol_ordinary .semicolon .statement) afterInitializer with
          ⟨sep1, afterSep1, sep1Result⟩ |
          ⟨failure, rejected, sep1Result⟩
        · have sep1Reply := symbol_validFor .semicolon .statement
            afterInitializer initializerReply.2.1
          rw [sep1Result] at sep1Reply
          have sep1Window := symbol_preservesTokenWindow .semicolon .statement
            afterInitializer
          rw [sep1Result] at sep1Window
          have sep1Progress : afterInitializer.cursor < afterSep1.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .semicolon) .statement
              (· == .symbol .semicolon) sep1Result
          have expressionAfterSep1 :
              afterSep1.remainingCount < expressionFuel :=
            remainingCount_lt_of_cursor_le sep1Window.2
              (Nat.le_of_lt sep1Progress) expressionAfterInitializer
          have statementAfterSep1 :
              afterSep1.remainingCount < statementFuel + 4 :=
            remainingCount_lt_after_strict_progress sep1Reply.2.1
              sep1Window.2 sep1Progress statementAfterInitializer
          rcases expressionContract.ordinary afterSep1 sep1Reply.2.1
              expressionAfterSep1 with
            ⟨condition, afterCondition, conditionResult⟩ |
            ⟨failure, rejected, conditionResult⟩
          · have conditionReply := expressionContract.validFor afterSep1
              sep1Reply.2.1
            rw [conditionResult] at conditionReply
            have conditionWindow := expressionContract.preservesTokenWindow
              afterSep1
            rw [conditionResult] at conditionWindow
            have conditionProgress :=
              expressionContract.cursorLtOnSuccess conditionResult
            have expressionAfterCondition :
                afterCondition.remainingCount < expressionFuel :=
              remainingCount_lt_of_cursor_le conditionWindow.2
                (Nat.le_of_lt conditionProgress) expressionAfterSep1
            have statementAfterCondition :
                afterCondition.remainingCount < statementFuel + 3 :=
              remainingCount_lt_after_strict_progress conditionReply.2.1
                conditionWindow.2 conditionProgress statementAfterSep1
            rcases (symbol_ordinary .semicolon .statement) afterCondition with
              ⟨sep2, afterSep2, sep2Result⟩ |
              ⟨failure, rejected, sep2Result⟩
            · have sep2Reply := symbol_validFor .semicolon .statement
                afterCondition conditionReply.2.1
              rw [sep2Result] at sep2Reply
              have sep2Window := symbol_preservesTokenWindow .semicolon
                .statement afterCondition
              rw [sep2Result] at sep2Window
              have sep2Progress : afterCondition.cursor < afterSep2.cursor :=
                acceptToken_cursor_lt_onSuccess (.symbol .semicolon)
                  .statement (· == .symbol .semicolon) sep2Result
              have expressionAfterSep2 :
                  afterSep2.remainingCount < expressionFuel :=
                remainingCount_lt_of_cursor_le sep2Window.2
                  (Nat.le_of_lt sep2Progress) expressionAfterCondition
              have statementAfterSep2 :
                  afterSep2.remainingCount < statementFuel + 2 :=
                remainingCount_lt_after_strict_progress sep2Reply.2.1
                  sep2Window.2 sep2Progress statementAfterCondition
              rcases postContract.ordinary afterSep2 sep2Reply.2.1
                  expressionAfterSep2 with
                ⟨post, afterPost, postResult⟩ |
                ⟨failure, rejected, postResult⟩
              · have postReply := postContract.validFor afterSep2
                    sep2Reply.2.1
                rw [postResult] at postReply
                have postWindow := postContract.preservesTokenWindow afterSep2
                rw [postResult] at postWindow
                have postCursor := postContract.cursorMonotoneOnSuccess
                  afterSep2 post afterPost postResult
                have statementAfterPost :
                    afterPost.remainingCount < statementFuel + 2 :=
                  remainingCount_lt_of_cursor_le postWindow.2 postCursor
                    statementAfterSep2
                rcases (symbol_ordinary .rightParen .statement) afterPost with
                  ⟨closing, afterClosing, closingResult⟩ |
                  ⟨failure, rejected, closingResult⟩
                · have closingReply := symbol_validFor .rightParen .statement
                      afterPost postReply.2.1
                  rw [closingResult] at closingReply
                  have closingWindow := symbol_preservesTokenWindow
                    .rightParen .statement afterPost
                  rw [closingResult] at closingWindow
                  have closingProgress :
                      afterPost.cursor < afterClosing.cursor :=
                    acceptToken_cursor_lt_onSuccess (.symbol .rightParen)
                      .statement (· == .symbol .rightParen) closingResult
                  have blockAdequate :
                      afterClosing.remainingCount < statementFuel + 1 :=
                    remainingCount_lt_after_strict_progress closingReply.2.1
                      closingWindow.2 closingProgress statementAfterPost
                  rcases blockContract.ordinary afterClosing closingReply.2.1
                      blockAdequate with
                    ⟨body, final, bodyResult⟩ |
                    ⟨failure, rejected, bodyResult⟩
                  · exact Or.inl ⟨{
                        span := SourceSpan.cover marker.span body.span
                        value := .forLoop
                          (SourceSpan.cover opening.span closing.span)
                          initializer condition post body
                      }, final, by
                        simp only [forStatement, bind, markerResult,
                          openingResult, initializerResult, sep1Result,
                          conditionResult, sep2Result, postResult,
                          closingResult, bodyResult, pure]⟩
                  · exact Or.inr ⟨failure, rejected, by
                      simp only [forStatement, bind, markerResult,
                        openingResult, initializerResult, sep1Result,
                        conditionResult, sep2Result, postResult,
                        closingResult, bodyResult]⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [forStatement, bind, markerResult,
                      openingResult, initializerResult, sep1Result,
                      conditionResult, sep2Result, postResult, closingResult]⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [forStatement, bind, markerResult, openingResult,
                    initializerResult, sep1Result, conditionResult,
                    sep2Result, postResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [forStatement, bind, markerResult, openingResult,
                  initializerResult, sep1Result, conditionResult, sep2Result]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [forStatement, bind, markerResult, openingResult,
                initializerResult, sep1Result, conditionResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [forStatement, bind, markerResult, openingResult,
              initializerResult, sep1Result]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [forStatement, bind, markerResult, openingResult,
            initializerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [forStatement, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [forStatement, bind, markerResult]⟩

/-- Adequate header and body fuel exclude every `for` invariant. -/
theorem forStatement_ne_invariant_of_fuels
    {itemValid : SourceFile → ForItem → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (initializerContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .semicolon)
        expressionFuel)
    (postContract : ControlInternals.ForItemsFuelTotalityContract
      itemValid (ControlInternals.forItems expression .rightParen)
        expressionFuel)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 7))
    (error : ParserInvariantError) :
    forStatement statement expression input ≠ .invariant error := by
  intro failed
  rcases forStatement_ordinary_of_fuels statement expression statementFuel
      expressionFuel initializerContract postContract expressionContract
        blockContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
