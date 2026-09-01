import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.MatchCasesFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.MatchDefaultFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.MatchScrutineeTotalityProperties
import Solcore.Syntax.Parser.Statement.MatchValidationTotalityProperties

/-! Fuel-aware ordinary control for a complete Core `match` statement. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace MatchInternals

/-- The outer budget shared by scrutinees, case arms, and default bodies. -/
def matchStatementFuel (expressionFuel caseFuel statementFuel : Nat) : Nat :=
  Nat.min (expressionFuel + 2)
    (Nat.min (caseFuel + 3) (statementFuel + 5))

private def finishMatchStatement (marker : Token)
    (scrutinees : NonemptyDelimitedList Expr) (opening : Token)
    (cases : List MatchCase) (defaultBody : Option Block)
    (closing : Token) : Parser Statement := do
  let armsSpan := SourceSpan.cover opening.span closing.span
  let _ ← validateMatchArities scrutinees.elements.toList.length cases
  if cases.isEmpty && defaultBody.isNone then
    let _ ← emitDiagnostic {
      span := SourceSpan.cover marker.span closing.span
      kind := .constraintViolation .matchRequiresArm
    }
  else
    pure ()
  pure {
    span := SourceSpan.cover marker.span closing.span
    value := .matchWith scrutinees {
      span := armsSpan
      value := { cases, defaultBody }
    }
  }

private theorem finishMatchStatement_ordinary (marker : Token)
    (scrutinees : NonemptyDelimitedList Expr) (opening : Token)
    (cases : List MatchCase) (defaultBody : Option Block)
    (closing : Token) :
    Parser.Ordinary
      (finishMatchStatement marker scrutinees opening cases defaultBody
        closing) := by
  intro input
  rcases validateMatchArities_ordinary scrutinees.elements.toList.length
      cases input with
    ⟨validated, afterValidation, validationResult⟩ |
    ⟨failure, rejected, validationResult⟩
  · cases validated
    let diagnostic : ParseDiagnostic := {
      span := SourceSpan.cover marker.span closing.span
      kind := .constraintViolation .matchRequiresArm
    }
    let retained : Statement := {
      span := SourceSpan.cover marker.span closing.span
      value := .matchWith scrutinees {
        span := SourceSpan.cover opening.span closing.span
        value := { cases, defaultBody }
      }
    }
    by_cases missing : cases.isEmpty && defaultBody.isNone
    · exact Or.inl ⟨retained, afterValidation.emit diagnostic, by
        unfold finishMatchStatement
        simp only [bind, validationResult]
        simp [missing, emitDiagnostic, modifyState, pure, diagnostic,
          retained]⟩
    · exact Or.inl ⟨retained, afterValidation, by
        unfold finishMatchStatement
        simp only [bind, validationResult]
        simp [missing, pure, retained]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [finishMatchStatement, bind, validationResult]⟩

end MatchInternals

/--
The complete match parser is ordinary below independent expression, case-arm,
and recursive-statement bounds.
-/
theorem matchStatement_ordinary_of_fuels
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    {caseValueValid : SourceFile → MatchCase → Prop}
    (statement : Parser Statement) (expression : Parser Expr)
    (pattern : Parser Pattern) (statementFuel expressionFuel caseFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (expressionContract : FuelElementTotalityContract
      expression expressionFuel)
    (caseContract : MatchInternals.FuelCaseListTotalityContract caseValueValid
      (fun input => MatchInternals.matchCases statement pattern
        (input.remainingCount + 1) [] input) caseFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      MatchInternals.matchStatementFuel expressionFuel caseFuel
        statementFuel) :
    (∃ value next,
      matchStatement statement expression pattern input = .ok value next) ∨
    (∃ failure next,
      matchStatement statement expression pattern input =
        .reject failure next) := by
  have expressionBudget : input.remainingCount < expressionFuel + 2 :=
    Nat.lt_of_lt_of_le adequate (Nat.min_le_left _ _)
  have tailBudget := Nat.lt_of_lt_of_le adequate (Nat.min_le_right _ _)
  have caseBudget : input.remainingCount < caseFuel + 3 :=
    Nat.lt_of_lt_of_le tailBudget (Nat.min_le_left _ _)
  have statementBudget : input.remainingCount < statementFuel + 5 :=
    Nat.lt_of_lt_of_le tailBudget (Nat.min_le_right _ _)
  rcases (keyword_ordinary .matchKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .matchKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .matchKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress := acceptToken_cursor_lt_onSuccess
      (.keyword .matchKw) .statement (· == .keyword .matchKw) markerResult
    have expressionAfterMarker :
        afterMarker.remainingCount < expressionFuel + 1 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress expressionBudget
    have caseAfterMarker : afterMarker.remainingCount < caseFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress caseBudget
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 4 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        markerProgress statementBudget
    rcases delimited_ordinary_of_elementFuel .leftParen .rightParen false
        expression .expression .statement expressionFuel expressionContract
          afterMarker markerReply.2.1 expressionAfterMarker with
      ⟨values, afterValues, valuesResult⟩ |
      ⟨failure, rejected, valuesResult⟩
    · have valuesReply := delimited_validFor (fun _ _ => True)
        .leftParen .rightParen false expression .expression .statement
          expressionContract.validFor
          expressionContract.preservesTokenWindow.preservesTokensOnSuccess
          afterMarker markerReply.2.1
      rw [valuesResult] at valuesReply
      have valuesWindow := delimited_preservesTokenWindow .leftParen
        .rightParen false expression .expression .statement
          expressionContract.preservesTokenWindow afterMarker
      rw [valuesResult] at valuesWindow
      have valuesProgress := delimitedWithPolicy_cursor_lt_onSuccess
        .leftParen .rightParen false true expression .expression .statement
          valuesResult
      have caseAfterValues : afterValues.remainingCount < caseFuel + 1 :=
        remainingCount_lt_after_strict_progress valuesReply.2.1
          valuesWindow.2 valuesProgress caseAfterMarker
      have statementAfterValues :
          afterValues.remainingCount < statementFuel + 3 :=
        remainingCount_lt_after_strict_progress valuesReply.2.1
          valuesWindow.2 valuesProgress statementAfterMarker
      rcases MatchInternals.requireScrutinees_ordinary values afterValues with
        ⟨scrutinees, afterScrutinees, requiredResult⟩ |
        ⟨failure, rejected, requiredResult⟩
      · have requiredReply := MatchInternals.requireScrutinees_validFor
          (fun _ _ => True) values afterValues valuesReply.2.1 (by
            simpa [valuesReply.2.2] using valuesReply.1)
        rw [requiredResult] at requiredReply
        have requiredWindow :=
          MatchInternals.requireScrutinees_preservesTokenWindow values
            afterValues
        rw [requiredResult] at requiredWindow
        have requiredCursor :=
          MatchInternals.requireScrutinees_cursorMonotoneOnSuccess values
            afterValues scrutinees afterScrutinees requiredResult
        have caseAfterRequired :
            afterScrutinees.remainingCount < caseFuel + 1 :=
          remainingCount_lt_of_cursor_le requiredWindow.2 requiredCursor
            caseAfterValues
        have statementAfterRequired :
            afterScrutinees.remainingCount < statementFuel + 3 :=
          remainingCount_lt_of_cursor_le requiredWindow.2 requiredCursor
            statementAfterValues
        rcases (symbol_ordinary .leftBrace .statement) afterScrutinees with
          ⟨opening, afterOpening, openingResult⟩ |
          ⟨failure, rejected, openingResult⟩
        · have openingReply := symbol_validFor .leftBrace .statement
            afterScrutinees requiredReply.2.1
          rw [openingResult] at openingReply
          have openingWindow := symbol_preservesTokenWindow .leftBrace
            .statement afterScrutinees
          rw [openingResult] at openingWindow
          have openingProgress := acceptToken_cursor_lt_onSuccess
            (.symbol .leftBrace) .statement (· == .symbol .leftBrace)
              openingResult
          have casesAdequate : afterOpening.remainingCount < caseFuel :=
            remainingCount_lt_after_strict_progress openingReply.2.1
              openingWindow.2 openingProgress caseAfterRequired
          have statementAfterOpening :
              afterOpening.remainingCount < statementFuel + 2 :=
            remainingCount_lt_after_strict_progress openingReply.2.1
              openingWindow.2 openingProgress statementAfterRequired
          rcases caseContract.ordinary afterOpening openingReply.2.1
              casesAdequate with
            ⟨cases, afterCases, casesResult⟩ |
            ⟨failure, rejected, casesResult⟩
          · have casesReply := caseContract.validFor afterOpening
              openingReply.2.1
            rw [casesResult] at casesReply
            have casesWindow := caseContract.preservesTokenWindow afterOpening
            rw [casesResult] at casesWindow
            have casesCursor := caseContract.cursorMonotoneOnSuccess
              afterOpening cases afterCases casesResult
            have defaultAdequate :
                afterCases.remainingCount < statementFuel + 2 :=
              remainingCount_lt_of_cursor_le casesWindow.2 casesCursor
                statementAfterOpening
            rcases MatchInternals.optionalDefaultBody_ordinary_of_statementFuel
                statement statementFuel statementContract statementStrict
                  afterCases casesReply.2.1 defaultAdequate with
              ⟨defaultBody, afterDefault, defaultResult⟩ |
              ⟨failure, rejected, defaultResult⟩
            · have defaultReply := MatchInternals.optionalDefaultBody_validFor
                expressionValueValid patternValueValid yulValueValid statement
                  statementContract.validFor
                  statementContract.preservesTokenWindow.preservesTokensOnSuccess
                  afterCases casesReply.2.1
              rw [defaultResult] at defaultReply
              rcases (symbol_ordinary .rightBrace .statement) afterDefault with
                ⟨closing, afterClosing, closingResult⟩ |
                ⟨failure, rejected, closingResult⟩
              · rcases MatchInternals.finishMatchStatement_ordinary marker
                    scrutinees opening cases defaultBody closing afterClosing with
                  ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
                · exact Or.inl ⟨value, final, by
                    simp only [matchStatement, bind, markerResult, valuesResult,
                      requiredResult, openingResult, casesResult, defaultResult,
                      closingResult]
                    simpa only [MatchInternals.finishMatchStatement, bind] using
                      finished⟩
                · exact Or.inr ⟨failure, rejected, by
                    simp only [matchStatement, bind, markerResult, valuesResult,
                      requiredResult, openingResult, casesResult, defaultResult,
                      closingResult]
                    simpa only [MatchInternals.finishMatchStatement, bind] using
                      finished⟩
              · exact Or.inr ⟨failure, rejected, by
                  simp only [matchStatement, bind, markerResult, valuesResult,
                    requiredResult, openingResult, casesResult, defaultResult,
                    closingResult]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [matchStatement, bind, markerResult, valuesResult,
                  requiredResult, openingResult, casesResult, defaultResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [matchStatement, bind, markerResult, valuesResult,
                requiredResult, openingResult, casesResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [matchStatement, bind, markerResult, valuesResult,
              requiredResult, openingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [matchStatement, bind, markerResult, valuesResult,
            requiredResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [matchStatement, bind, markerResult, valuesResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [matchStatement, bind, markerResult]⟩

end Solcore.Syntax.Parser
