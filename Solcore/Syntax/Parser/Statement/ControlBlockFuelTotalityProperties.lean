import Solcore.Syntax.Parser.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionLayerConcreteFuelContractProperties
import Solcore.Syntax.Parser.Statement.ControlProperties

/-! Fuel-aware totality for braced and `while` Core statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A braced statement has the same ordinary outcomes as its Core block. -/
theorem blockStatement_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ value next, blockStatement statement input = .ok value next) ∨
      (∃ failure next,
        blockStatement statement input = .reject failure next) := by
  rcases coreBlock_ordinary_of_statementFuel statement .require statementFuel
      contract statementStrict input inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{ span := body.span, value := .block body.value }, next, by
      simp only [blockStatement, bind, result, pure]⟩
  · exact Or.inr ⟨failure, next, by
      simp only [blockStatement, bind, result]⟩

/-- Adequate recursive statement fuel excludes block-wrapper invariants. -/
theorem blockStatement_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    blockStatement statement input ≠ .invariant error := by
  intro failed
  rcases blockStatement_ordinary_of_statementFuel statement statementFuel
      contract statementStrict input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package a braced statement at one unit above recursive statement fuel. -/
theorem blockStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (blockStatement statement) (statementFuel + 1) := {
  validFor := blockStatement_validFor statement (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor contract.validFor
      contract.preservesTokenWindow.preservesTokensOnSuccess
  preservesTokenWindow := blockStatement_preservesTokenWindow statement
    contract.preservesTokenWindow
  cursorMonotoneOnSuccess :=
    blockStatement_cursorMonotoneOnSuccess statement
  startsAtCurrentTokenOnSuccess :=
    blockStatement_startsAtCurrentTokenOnSuccess statement
  ordinary := blockStatement_ordinary_of_statementFuel statement statementFuel
    contract statementStrict
}

/--
`while` needs two leading tokens before its expression and four strict prefix
steps before the recursive block. The smaller adequate budget serves both.
-/
theorem whileStatement_ordinary_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5)) :
    (∃ value next,
      whileStatement statement expression input = .ok value next) ∨
    (∃ failure next,
      whileStatement statement expression input = .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (expressionFuel + 2) (statementFuel + 5))
  have statementBudget : input.remainingCount < statementFuel + 5 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (expressionFuel + 2) (statementFuel + 5))
  rcases (contextual_ordinary .while .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := contextual_validFor .while .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := contextual_preservesTokenWindow .while .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.contextual .while) .statement
        (·.isContextual .while) markerResult
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
          rcases coreBlock_ordinary_of_statementFuel statement .require
              statementFuel statementContract statementStrict afterClosing
                closingReply.2.1 blockAdequate with
            ⟨body, final, bodyResult⟩ |
            ⟨failure, rejected, bodyResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span body.span
                value := .whileLoop condition body
              }, final, by
                simp only [whileStatement, bind, markerResult, openingResult,
                  conditionResult, closingResult, bodyResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [whileStatement, bind, markerResult, openingResult,
                conditionResult, closingResult, bodyResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [whileStatement, bind, markerResult, openingResult,
              conditionResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [whileStatement, bind, markerResult, openingResult,
            conditionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [whileStatement, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [whileStatement, bind, markerResult]⟩

/-- Adequacy for both recursive parsers excludes every `while` invariant. -/
theorem whileStatement_ne_invariant_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (statementFuel expressionFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract :
      FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (expressionFuel + 2) (statementFuel + 5))
    (error : ParserInvariantError) :
    whileStatement statement expression input ≠ .invariant error := by
  intro failed
  rcases whileStatement_ordinary_of_fuels statement expression statementFuel
      expressionFuel statementContract statementStrict expressionContract
        input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package canonical `while` syntax under both recursive fuel bounds. -/
theorem whileStatement_fuelTotalityContract
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
      (whileStatement statement expression)
      (Nat.min (expressionFuel + 2) (statementFuel + 5)) := {
  validFor := whileStatement_validFor (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor statement expression
      statementContract.validFor
      statementContract.preservesTokenWindow.preservesTokensOnSuccess
      expressionSyntax.validFor expressionSyntax.preservesTokensOnSuccess
      expressionSyntax.cursorMonotoneOnSuccess
  preservesTokenWindow := whileStatement_preservesTokenWindow statement
    expression statementContract.preservesTokenWindow
      expressionSyntax.preservesTokenWindow
  cursorMonotoneOnSuccess := whileStatement_cursorMonotoneOnSuccess statement
    expression expressionSyntax.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    whileStatement_startsAtCurrentTokenOnSuccess statement expression
  ordinary := whileStatement_ordinary_of_fuels statement expression
    statementFuel expressionFuel statementContract statementStrict
      expressionTotality
}

end Solcore.Syntax.Parser
