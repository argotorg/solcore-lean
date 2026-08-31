import Solcore.Syntax.Parser.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.MatchProperties

/-! Fuel-aware totality for one canonical Core `case` arm. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/--
One `case` marker reaches its pattern after one strict token step; a successful
pattern supplies the second strict step needed to enter the recursive block.
-/
theorem matchCase_ordinary_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (patternFuel + 1) (statementFuel + 3)) :
    (∃ value next, matchCase statement patternParser input = .ok value next) ∨
      (∃ failure next,
        matchCase statement patternParser input = .reject failure next) := by
  have patternBudget : input.remainingCount < patternFuel + 1 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_left (patternFuel + 1) (statementFuel + 3))
  have statementBudget : input.remainingCount < statementFuel + 3 :=
    Nat.lt_of_lt_of_le adequate
      (Nat.min_le_right (patternFuel + 1) (statementFuel + 3))
  rcases (keyword_ordinary .caseKw .statement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .caseKw .statement input inputValid
    rw [markerResult] at markerReply
    have markerWindow :=
      keyword_preservesTokenWindow .caseKw .statement input
    rw [markerResult] at markerWindow
    have markerProgress : input.cursor < afterMarker.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .caseKw) .statement
        (· == .keyword .caseKw) markerResult
    have patternAdequate : afterMarker.remainingCount < patternFuel :=
      remainingCount_lt_after_strict_progress markerReply.2.1
        markerWindow.2 markerProgress patternBudget
    have statementAfterMarker :
        afterMarker.remainingCount < statementFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1
        markerWindow.2 markerProgress statementBudget
    rcases patternContract.ordinary afterMarker markerReply.2.1
        patternAdequate with
      ⟨retainedPattern, afterPattern, patternResult⟩ |
      ⟨failure, rejected, patternResult⟩
    · have patternReply := patternContract.validFor afterMarker
        markerReply.2.1
      rw [patternResult] at patternReply
      have patternWindow := patternContract.preservesTokenWindow afterMarker
      rw [patternResult] at patternWindow
      have bodyAdequate :
          afterPattern.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress patternReply.2.1
          patternWindow.2
          (patternContract.cursorLtOnSuccess patternResult)
          statementAfterMarker
      rcases coreBlock_ordinary_of_statementFuel statement .require
          statementFuel statementContract statementStrict afterPattern
            patternReply.2.1 bodyAdequate with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := { pattern := retainedPattern, body }
          }, final, by
            simp only [matchCase, bind, markerResult, patternResult,
              bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [matchCase, bind, markerResult, patternResult,
            bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [matchCase, bind, markerResult, patternResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [matchCase, bind, markerResult]⟩

/-- Adequate pattern and recursive-statement fuels exclude every invariant. -/
theorem matchCase_ne_invariant_of_fuels
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount <
      Nat.min (patternFuel + 1) (statementFuel + 3))
    (error : ParserInvariantError) :
    matchCase statement patternParser input ≠ .invariant error := by
  intro failed
  rcases matchCase_ordinary_of_fuels statement patternParser statementFuel
      patternFuel statementContract statementStrict patternContract input
        inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Every successful `case` strictly consumes its leading marker. -/
theorem matchCase_cursor_lt_onSuccess
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (patternCursor : Parser.CursorMonotoneOnSuccess patternParser)
    {input final : State} {value : MatchCase}
    (parsed : matchCase statement patternParser input = .ok value final) :
    input.cursor < final.cursor := by
  unfold matchCase at parsed
  cases markerResult : keyword .caseKw .statement input with
  | reject failure rejected => simp [bind, markerResult] at parsed
  | invariant error => simp [bind, markerResult] at parsed
  | ok marker afterMarker =>
      simp only [bind, markerResult] at parsed
      cases patternResult : patternParser afterMarker with
      | reject failure rejected => simp [patternResult] at parsed
      | invariant error => simp [patternResult] at parsed
      | ok retainedPattern afterPattern =>
          simp only [patternResult] at parsed
          cases bodyResult : coreBlock statement .require afterPattern with
          | reject failure rejected => simp [bodyResult] at parsed
          | invariant error => simp [bodyResult] at parsed
          | ok body afterBody =>
              simp only [bodyResult, pure] at parsed
              have progress : input.cursor < afterBody.cursor :=
                Nat.lt_of_lt_of_le
                  (acceptToken_cursor_lt_onSuccess (.keyword .caseKw)
                    .statement (· == .keyword .caseKw) markerResult)
                  (Nat.le_trans
                    (patternCursor afterMarker retainedPattern afterPattern
                      patternResult)
                    (coreBlock_cursorMonotoneOnSuccess statement .require
                      afterPattern body afterBody bodyResult))
              cases parsed
              exact progress

/-- Package one Core case arm under its two independent recursive bounds. -/
theorem matchCase_fuelElementTotalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternValid : patternParser.ValidFor patternValueValid)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel) :
    FuelElementTotalityContract (matchCase statement patternParser)
      (Nat.min (patternFuel + 1) (statementFuel + 3)) := {
  validFor := (matchCase_validFor expressionValueValid patternValueValid
    yulValueValid statement patternParser statementContract.validFor
      statementContract.preservesTokenWindow.preservesTokensOnSuccess
      patternValid
      patternContract.preservesTokenWindow.preservesTokensOnSuccess
      (fun {_input _value _next} parsed =>
        Nat.le_of_lt (patternContract.cursorLtOnSuccess parsed))).mono
          (fun _ _ _ => trivial)
  preservesTokenWindow := matchCase_preservesTokenWindow statement
    patternParser statementContract.preservesTokenWindow
      patternContract.preservesTokenWindow
  cursorLtOnSuccess := matchCase_cursor_lt_onSuccess statement patternParser
    (fun {_input _value _next} parsed =>
      Nat.le_of_lt (patternContract.cursorLtOnSuccess parsed))
  ordinary := matchCase_ordinary_of_fuels statement patternParser
    statementFuel patternFuel statementContract statementStrict
      patternContract
}

end Solcore.Syntax.Parser.MatchInternals
