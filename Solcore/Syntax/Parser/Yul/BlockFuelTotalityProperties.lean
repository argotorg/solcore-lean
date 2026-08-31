import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.Common

/-! Fuel-aware totality for braced inline-Yul statement sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeYulBlock_ordinary (opening : Token)
    (bodyRev : List YulStmt) :
    Parser.Ordinary (closeYulBlock opening bodyRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .yulStatement) input with
    ⟨closing, next, closingResult⟩ | ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
        span := SourceSpan.cover opening.span closing.span
        body := bodyRev.reverse
      }, next, by
        unfold closeYulBlock
        simp only [closingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold closeYulBlock
      simp only [closingResult]⟩

/-- Loop and recursive-statement fuel jointly exclude every block invariant. -/
theorem yulBlockItems_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (opening : Token) :
    ∀ loopFuel bodyRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < statementFuel →
      (∃ body final,
        yulBlockItems statement opening loopFuel bodyRev input =
          .ok body final) ∨
      (∃ failure final,
        yulBlockItems statement opening loopFuel bodyRev input =
          .reject failure final) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      unfold yulBlockItems
      split
      · exact closeYulBlock_ordinary opening bodyRev input
      · split
        · have atEnd : input.atEnd = true := by assumption
          have cursorAtEnd : input.window.endIndex ≤ input.cursor := by
            simpa [State.atEnd] using atEnd
          have peekNone : input.peek? = none := by
            unfold State.peek?
            simp [Nat.not_lt_of_ge cursorAtEnd]
          cases closingResult : symbol .rightBrace .yulStatement input with
          | ok closing next =>
              simp [symbol, acceptToken, peekNone, rejectAt] at closingResult
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | invariant error =>
              exact False.elim
                ((symbol_ordinary .rightBrace .yulStatement).ne_invariant
                  input error closingResult)
        · cases statementResult : statement input with
          | invariant error =>
              exact False.elim
                (contract.ne_invariant input inputValid statementAdequate
                  error statementResult)
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | ok value next =>
              have replyValid := contract.validFor input inputValid
              rw [statementResult] at replyValid
              have replyWindow := contract.preservesTokenWindow input
              rw [statementResult] at replyWindow
              have progress := contract.cursorLtOnSuccess statementResult
              have nextLoopAdequate : next.remainingCount < loopFuel :=
                remainingCount_lt_after_strict_progress replyValid.2.1
                  replyWindow.2 progress loopAdequate
              have nextStatementAdequate :
                  next.remainingCount < statementFuel :=
                remainingCount_lt_of_cursor_le replyWindow.2
                  (Nat.le_of_lt progress) statementAdequate
              dsimp only
              split
              · exact inductionHypothesis (value :: bodyRev) next
                  replyValid.2.1 nextLoopAdequate nextStatementAdequate
              · omega

theorem yulBlockItems_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (opening : Token) (loopFuel : Nat) (bodyRev : List YulStmt)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (statementAdequate : input.remainingCount < statementFuel)
    (error : ParserInvariantError) :
    yulBlockItems statement opening loopFuel bodyRev input ≠
      .invariant error := by
  intro failed
  rcases yulBlockItems_ordinary_of_statementFuel statement statementFuel
      contract opening loopFuel bodyRev input inputValid loopAdequate
        statementAdequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The opening brace supplies the one extra unit of statement fuel. -/
theorem yulBlock_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body final, yulBlock statement input = .ok body final) ∨
    (∃ failure final,
      yulBlock statement input = .reject failure final) := by
  rcases (symbol_ordinary .leftBrace .yulStatement) input with
    ⟨opening, afterOpening, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .yulStatement input
      inputValid
    rw [openingResult] at openingReply
    have openingWindow :=
      symbol_preservesTokenWindow .leftBrace .yulStatement input
    rw [openingResult] at openingWindow
    have openingProgress : input.cursor < afterOpening.cursor :=
      acceptToken_cursor_lt_onSuccess (.symbol .leftBrace) .yulStatement
        (· == .symbol .leftBrace) openingResult
    have statementAdequate :
        afterOpening.remainingCount < statementFuel :=
      remainingCount_lt_after_strict_progress openingReply.2.1
        openingWindow.2 openingProgress adequate
    simpa only [yulBlock, openingResult] using
      yulBlockItems_ordinary_of_statementFuel statement statementFuel
        contract opening (afterOpening.remainingCount + 1) [] afterOpening
          openingReply.2.1 (by omega) statementAdequate
  · exact Or.inr ⟨failure, rejected, by
      simp only [yulBlock, openingResult]⟩

theorem yulBlock_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    yulBlock statement input ≠ .invariant error := by
  intro failed
  rcases yulBlock_ordinary_of_statementFuel statement statementFuel contract
      input inputValid adequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Package a recursive-fuel Yul block for statement-layer recursion. -/
theorem yulBlock_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (contract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (yulBlock statement)
      (statementFuel + 1) := {
  validFor := (yulBlock_validFor (fun _ _ => True) statement
    contract.validFor
      contract.preservesTokenWindow.preservesTokensOnSuccess).mono
        (fun _ _ _ => trivial)
  preservesTokenWindow := yulBlock_preservesTokenWindow statement
    contract.preservesTokenWindow
  cursorLtOnSuccess := yulBlock_cursor_lt_onSuccess statement
    contract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulBlock_ordinary_of_statementFuel statement statementFuel
    contract
}

end Solcore.Syntax.Parser
