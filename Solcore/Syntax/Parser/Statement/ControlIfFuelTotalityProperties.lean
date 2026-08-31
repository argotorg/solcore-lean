import Solcore.Syntax.Parser.Statement.ControlBlockFuelTotalityProperties

/-! Fuel-aware totality for Core `if` statements and optional `else` bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ControlInternals

/-- Optional `else` parsing reuses the already fuel-bounded Core block. -/
theorem optionalElseBody_ordinary_of_blockFuel
    (statement : Parser Statement) (statementFuel : Nat)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body next, optionalElseBody statement input = .ok body next) ∨
      (∃ failure next,
        optionalElseBody statement input = .reject failure next) := by
  unfold optionalElseBody
  simp only [getState, bind]
  split
  · rcases (keyword_ordinary .elseKw .statement) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := keyword_validFor .elseKw .statement input
        inputValid
      rw [markerResult] at markerReply
      have markerWindow :=
        keyword_preservesTokenWindow .elseKw .statement input
      rw [markerResult] at markerWindow
      have bodyAdequate :
          afterMarker.remainingCount < statementFuel + 1 := by
        have spent : afterMarker.remainingCount < statementFuel :=
          remainingCount_lt_after_strict_progress markerReply.2.1
            markerWindow.2
            (acceptToken_cursor_lt_onSuccess (.keyword .elseKw) .statement
              (· == .keyword .elseKw) markerResult) adequate
        omega
      rcases blockContract.ordinary afterMarker markerReply.2.1 bodyAdequate
          with ⟨body, final, bodyResult⟩ |
            ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨some body, final, by
          simp only [markerResult, bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [markerResult, bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [markerResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

end ControlInternals

/--
The same prefix budget used by `while` reaches the condition and then block;
strict then-block progress leaves enough fuel for a present `else` block.
-/
theorem ifStatement_ordinary_of_fuels
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5)) :
    (∃ value next, ifStatement statement expression input = .ok value next) ∨
      (∃ failure next,
        ifStatement statement expression input = .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (expressionFuel + 2) (statementFuel + 5))
  have statementBudget : input.remainingCount < statementFuel + 5 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (expressionFuel + 2) (statementFuel + 5))
  rcases (keyword_ordinary .ifKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .ifKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .ifKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .ifKw) .statement
        (· == .keyword .ifKw) markerResult
    have expressionAfterMarker :
        afterMarker.remainingCount < expressionFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress (by omega)
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 4 :=
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
      have expressionAdequate :
          afterOpening.remainingCount < expressionFuel :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      have statementAfterOpening :
          afterOpening.remainingCount < statementFuel + 3 :=
        remainingCount_lt_after_strict_progress openingReply.2.1
          openingWindow.2 openingProgress (by omega)
      rcases expressionContract.ordinary afterOpening openingReply.2.1
          expressionAdequate with
        ⟨condition, afterCondition, conditionResult⟩ |
        ⟨failure, rejected, conditionResult⟩
      · have conditionReply := expressionContract.validFor afterOpening
          openingReply.2.1
        rw [conditionResult] at conditionReply
        have conditionWindow := expressionContract.preservesTokenWindow
          afterOpening
        rw [conditionResult] at conditionWindow
        have conditionProgress :=
          expressionContract.cursorLtOnSuccess conditionResult
        have statementAfterCondition :
            afterCondition.remainingCount < statementFuel + 2 :=
          remainingCount_lt_after_strict_progress conditionReply.2.1
            conditionWindow.2 conditionProgress (by omega)
        rcases (symbol_ordinary .rightParen .statement) afterCondition with
          ⟨closing, afterClosing, closingResult⟩ |
          ⟨failure, rejected, closingResult⟩
        · have closingReply := symbol_validFor .rightParen .statement
            afterCondition conditionReply.2.1
          rw [closingResult] at closingReply
          have closingWindow :=
            symbol_preservesTokenWindow .rightParen .statement afterCondition
          rw [closingResult] at closingWindow
          have closingProgress : afterCondition.cursor < afterClosing.cursor :=
            acceptToken_cursor_lt_onSuccess (.symbol .rightParen) .statement
              (· == .symbol .rightParen) closingResult
          have blockAdequate :
              afterClosing.remainingCount < statementFuel + 1 :=
            remainingCount_lt_after_strict_progress closingReply.2.1
              closingWindow.2 closingProgress (by omega)
          rcases blockContract.ordinary afterClosing closingReply.2.1
              blockAdequate with
            ⟨thenBody, afterThen, thenResult⟩ |
            ⟨failure, rejected, thenResult⟩
          · have thenReply := blockContract.validFor afterClosing
              closingReply.2.1
            rw [thenResult] at thenReply
            have thenWindow := blockContract.preservesTokenWindow afterClosing
            rw [thenResult] at thenWindow
            have thenProgress := blockContract.cursorLtOnSuccess thenResult
            have elseAdequate :
                afterThen.remainingCount < statementFuel + 1 := by
              have spent : afterThen.remainingCount < statementFuel :=
                remainingCount_lt_after_strict_progress thenReply.2.1
                  thenWindow.2 thenProgress blockAdequate
              omega
            rcases ControlInternals.optionalElseBody_ordinary_of_blockFuel
                statement statementFuel blockContract afterThen thenReply.2.1
                  elseAdequate with
              ⟨elseBody, final, elseResult⟩ |
              ⟨failure, rejected, elseResult⟩
            · let endSpan := elseBody.map (fun body => body.span)
                  |>.getD thenBody.span
              exact Or.inl ⟨{
                  span := SourceSpan.cover marker.span endSpan
                  value := .ifThen condition thenBody elseBody
                }, final, by
                  simp only [ifStatement, bind, markerResult, openingResult,
                    conditionResult, closingResult, thenResult, elseResult,
                    pure, endSpan]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [ifStatement, bind, markerResult, openingResult,
                  conditionResult, closingResult, thenResult, elseResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [ifStatement, bind, markerResult, openingResult,
                conditionResult, closingResult, thenResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [ifStatement, bind, markerResult, openingResult,
              conditionResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [ifStatement, bind, markerResult, openingResult,
            conditionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [ifStatement, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [ifStatement, bind, markerResult]⟩

/-- Adequate expression and recursive statement fuel exclude invariants. -/
theorem ifStatement_ne_invariant_of_fuels
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (blockContract : FuelElementTotalityContract
      (coreBlock statement .require) (statementFuel + 1))
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5))
    (error : ParserInvariantError) :
    ifStatement statement expression input ≠ .invariant error := by
  intro failed
  rcases ifStatement_ordinary_of_fuels statement expression statementFuel
      expressionFuel blockContract expressionContract input inputValid
        adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package canonical `if` syntax under both recursive fuel bounds. -/
theorem ifStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (ifStatement statement expression)
      (Nat.min (expressionFuel + 2) (statementFuel + 5)) := by
  let blockContract := coreBlock_fuelTotalityContract statement .require
    statementFuel statementContract statementStrict
      (fun _ _ valid => valid.span_valid)
  exact {
    validFor := ifStatement_validFor (Expr.ValidFor statementValid)
      patternValueValid YulStmt.ValidFor statement expression
        statementContract.validFor
        statementContract.preservesTokenWindow.preservesTokensOnSuccess
        expressionSyntax.validFor expressionSyntax.preservesTokensOnSuccess
        expressionSyntax.cursorMonotoneOnSuccess
    preservesTokenWindow := ifStatement_preservesTokenWindow statement
      expression statementContract.preservesTokenWindow
        expressionSyntax.preservesTokenWindow
    cursorMonotoneOnSuccess := ifStatement_cursorMonotoneOnSuccess statement
      expression expressionSyntax.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      ifStatement_startsAtCurrentTokenOnSuccess statement expression
    ordinary := ifStatement_ordinary_of_fuels statement expression
      statementFuel expressionFuel blockContract expressionTotality
  }

end Solcore.Syntax.Parser
