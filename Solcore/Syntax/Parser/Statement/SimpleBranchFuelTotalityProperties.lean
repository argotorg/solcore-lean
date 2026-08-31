import Solcore.Syntax.Parser.Statement.SimpleBranchTotalityProperties
import Solcore.Syntax.Parser.TermStatementFallbackFuelTotalityProperties

/-! Recursive-fuel totality for Core `let` and `return` statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

theorem optionalLetInitializer_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ value next, optionalLetInitializer expression input = .ok value next) ∨
    (∃ failure next,
      optionalLetInitializer expression input = .reject failure next) := by
  by_cases present : isSymbol input .equal
  · rcases (symbol_ordinary .equal .statement) input with
      ⟨equal, afterEqual, equalResult⟩ |
      ⟨failure, rejected, equalResult⟩
    · have equalReply := symbol_validFor .equal .statement input inputValid
      rw [equalResult] at equalReply
      have equalWindow := symbol_preservesTokenWindow .equal .statement input
      rw [equalResult] at equalWindow
      have expressionAdequate : afterEqual.remainingCount < expressionFuel :=
        remainingCount_lt_of_cursor_le equalWindow.2
          (symbol_cursorMonotoneOnSuccess .equal .statement input equal
            afterEqual equalResult) adequate
      rcases contract.ordinary afterEqual equalReply.2.1
          expressionAdequate with
        ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
      · exact Or.inl ⟨some value, next, by
          simp only [optionalLetInitializer, getState, bind, present,
            ↓reduceIte, equalResult, valueResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [optionalLetInitializer, getState, bind, present,
            ↓reduceIte, equalResult, valueResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalLetInitializer, getState, bind, present,
          ↓reduceIte, equalResult]⟩
  · have absent : isSymbol input .equal = false := by
      cases found : isSymbol input .equal with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalLetInitializer, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem optionalReturnValue_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel) :
    (∃ value next, optionalReturnValue expression input = .ok value next) ∨
    (∃ failure next,
      optionalReturnValue expression input = .reject failure next) := by
  by_cases empty : isSymbol input .semicolon
  · exact Or.inl ⟨none, input, by
      simp only [optionalReturnValue, getState, bind, empty, ↓reduceIte, pure]⟩
  · have nonempty : isSymbol input .semicolon = false := by
      cases found : isSymbol input .semicolon with
      | false => rfl
      | true => exact False.elim (empty found)
    rcases contract.ordinary input inputValid adequate with
      ⟨value, next, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · exact Or.inl ⟨some value, next, by
        simp only [optionalReturnValue, getState, bind, nonempty,
          Bool.false_eq_true, ↓reduceIte, valueResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalReturnValue, getState, bind, nonempty,
          Bool.false_eq_true, ↓reduceIte, valueResult]⟩

end Solcore.Syntax.Parser.StatementSimpleInternals

namespace Solcore.Syntax.Parser

theorem letStatement_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ statement next, letStatement expression input = .ok statement next) ∨
    (∃ failure next, letStatement expression input = .reject failure next) := by
  rcases (keyword_ordinary .letKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .letKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .letKw .statement input
    rw [markerResult] at markerWindow
    have afterMarkerAdequate : afterMarker.remainingCount < expressionFuel :=
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
      rcases StatementSimpleInternals.optionalLetType_invariantFreeOnValid
          afterName nameReply.2.1 with
        ⟨type, afterType, typeResult⟩ | ⟨failure, rejected, typeResult⟩
      · have typeReply := StatementSimpleInternals.optionalLetType_validFor
          afterName nameReply.2.1
        rw [typeResult] at typeReply
        have typeWindow :=
          StatementSimpleInternals.optionalLetType_preservesTokenWindow afterName
        rw [typeResult] at typeWindow
        have afterTypeAdequate : afterType.remainingCount < expressionFuel :=
          remainingCount_lt_of_cursor_le typeWindow.2
            (StatementSimpleInternals.optionalLetType_cursorMonotoneOnSuccess
              afterName type afterType typeResult) afterNameAdequate
        rcases StatementSimpleInternals.optionalLetInitializer_ordinary_of_expressionFuel
            expression expressionFuel contract afterType typeReply.2.1
              afterTypeAdequate with
          ⟨initializer, afterInitializer, initializerResult⟩ |
          ⟨failure, rejected, initializerResult⟩
        · have initializerReply :=
            StatementSimpleInternals.optionalLetInitializer_validFor expression
              (fun _ _ => True) contract.validFor afterType typeReply.2.1
          rw [initializerResult] at initializerReply
          rcases (symbol_ordinary .semicolon .statement) afterInitializer with
            ⟨semicolon, final, semicolonResult⟩ |
            ⟨failure, rejected, semicolonResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover marker.span semicolon.span
                value := .letDecl name type initializer
              }, final, by
                simp only [letStatement, bind, markerResult, nameResult,
                  typeResult, initializerResult, semicolonResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [letStatement, bind, markerResult, nameResult,
                typeResult, initializerResult, semicolonResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [letStatement, bind, markerResult, nameResult,
              typeResult, initializerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [letStatement, bind, markerResult, nameResult, typeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [letStatement, bind, markerResult, nameResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [letStatement, bind, markerResult]⟩

theorem returnStatement_ordinary_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1) :
    (∃ statement next,
      returnStatement expression input = .ok statement next) ∨
    (∃ failure next,
      returnStatement expression input = .reject failure next) := by
  rcases (keyword_ordinary .returnKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .returnKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .returnKw .statement input
    rw [markerResult] at markerWindow
    have valueAdequate : afterMarker.remainingCount < expressionFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .returnKw) .statement
          (· == .keyword .returnKw) markerResult) adequate
    rcases StatementSimpleInternals.optionalReturnValue_ordinary_of_expressionFuel
        expression expressionFuel contract afterMarker markerReply.2.1
          valueAdequate with
      ⟨value, afterValue, valueResult⟩ | ⟨failure, rejected, valueResult⟩
    · have valueReply := StatementSimpleInternals.optionalReturnValue_validFor
        expression (fun _ _ => True) contract.validFor afterMarker
          markerReply.2.1
      rw [valueResult] at valueReply
      rcases (symbol_ordinary .semicolon .statement) afterValue with
        ⟨semicolon, final, semicolonResult⟩ |
        ⟨failure, rejected, semicolonResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span semicolon.span
            value := .returnStmt value
          }, final, by
            simp only [returnStatement, bind, markerResult, valueResult,
              semicolonResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [returnStatement, bind, markerResult, valueResult,
            semicolonResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [returnStatement, bind, markerResult, valueResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [returnStatement, bind, markerResult]⟩

theorem letStatement_ne_invariant_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    letStatement expression input ≠ .invariant error := by
  intro failed
  rcases letStatement_ordinary_of_expressionFuel expression expressionFuel
      contract input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem returnStatement_ne_invariant_of_expressionFuel
    (expression : Parser Expr) (expressionFuel : Nat)
    (contract : FuelElementTotalityContract expression expressionFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < expressionFuel + 1)
    (error : ParserInvariantError) :
    returnStatement expression input ≠ .invariant error := by
  intro failed
  rcases returnStatement_ordinary_of_expressionFuel expression expressionFuel
      contract input inputValid adequate with
    ⟨statement, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem letStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (totality : FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (letStatement expression) (expressionFuel + 1) := {
  validFor := letStatement_validFor expression (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor expressionSyntax.validFor
      expressionSyntax.preservesTokenWindow
        expressionSyntax.cursorMonotoneOnSuccess
  preservesTokenWindow := letStatement_preservesTokenWindow expression
    expressionSyntax.preservesTokenWindow
  cursorMonotoneOnSuccess := letStatement_cursorMonotoneOnSuccess expression
    expressionSyntax.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    letStatement_startsAtCurrentTokenOnSuccess expression
  ordinary := letStatement_ordinary_of_expressionFuel expression
    expressionFuel totality
}

theorem returnStatement_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (patternValueValid : SourceFile → Pattern → Prop)
    (expression : Parser Expr) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (totality : FuelElementTotalityContract expression expressionFuel) :
    TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor (Expr.ValidFor statementValid)
        patternValueValid YulStmt.ValidFor)
      (returnStatement expression) (expressionFuel + 1) := {
  validFor := returnStatement_validFor expression (Expr.ValidFor statementValid)
    patternValueValid YulStmt.ValidFor expressionSyntax.validFor
      expressionSyntax.preservesTokenWindow
        expressionSyntax.cursorMonotoneOnSuccess
  preservesTokenWindow := returnStatement_preservesTokenWindow expression
    expressionSyntax.preservesTokenWindow
  cursorMonotoneOnSuccess := returnStatement_cursorMonotoneOnSuccess expression
    expressionSyntax.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    returnStatement_startsAtCurrentTokenOnSuccess expression
  ordinary := returnStatement_ordinary_of_expressionFuel expression
    expressionFuel totality
}

end Solcore.Syntax.Parser
