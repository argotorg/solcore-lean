import Solcore.Syntax.Parser.Yul.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.ControlFunctionFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.LeafTotalityProperties

/-! Fuel-aware totality for the internal arms of inline-Yul switches. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace YulControl

/-- Fuel-bounded totality for helpers which may succeed without consuming. -/
structure FuelParserTotalityContract {alpha : Type}
    (parser : Parser alpha) (fuel : Nat) : Prop where
  validFor : parser.ValidFor (fun _ _ => True)
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelParserTotalityContract

theorem ne_invariant {alpha : Type} {parser : Parser alpha} {fuel : Nat}
    (contract : FuelParserTotalityContract parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end FuelParserTotalityContract

end YulControl

private theorem yulCase_weakValidFor (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (YulControl.caseArm statement).ValidFor (fun _ _ => True) := by
  unfold YulControl.caseArm
  apply Parser.bind_validFor (keyword_validFor .caseKw .yulStatement)
  intro marker
  apply Parser.bind_validFor yulLiteral_elementTotalityContract.validFor
  intro literal
  apply Parser.bind_validFor
    (yulBlock_validFor (fun _ _ => True) statement statementValid
      statementWindow.preservesTokensOnSuccess)
  intro body
  exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/-- A `case`, its literal, and its block spend three wrapper fuel units. -/
theorem yulCase_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3) :
    (∃ value next, YulControl.caseArm statement input = .ok value next) ∨
      (∃ failure next,
        YulControl.caseArm statement input = .reject failure next) := by
  rcases (keyword_ordinary .caseKw .yulStatement) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerReply := keyword_validFor .caseKw .yulStatement input inputValid
    rw [markerResult] at markerReply
    have markerWindow := keyword_preservesTokenWindow .caseKw .yulStatement input
    rw [markerResult] at markerWindow
    have literalBudget : afterMarker.remainingCount < statementFuel + 2 :=
      remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.keyword .caseKw) .yulStatement
          (· == .keyword .caseKw) markerResult) adequate
    rcases yulLiteral_ordinary afterMarker with
      ⟨literal, afterLiteral, literalResult⟩ |
      ⟨failure, rejected, literalResult⟩
    · have literalReply := yulLiteral_elementTotalityContract.validFor
        afterMarker markerReply.2.1
      rw [literalResult] at literalReply
      have literalWindow := yulLiteral_preservesTokenWindow afterMarker
      rw [literalResult] at literalWindow
      have bodyBudget : afterLiteral.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress literalReply.2.1
          literalWindow.2 (yulLiteral_cursor_lt_onSuccess literalResult)
            literalBudget
      rcases (yulBlock_fuelElementTotalityContract statement statementFuel
          statementContract).ordinary afterLiteral literalReply.2.1 bodyBudget with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨{
            span := SourceSpan.cover marker.span body.span
            value := .arm literal body.body
          }, final, by
            simp only [YulControl.caseArm, bind, markerResult, literalResult,
              bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [YulControl.caseArm, bind, markerResult, literalResult,
            bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [YulControl.caseArm, bind, markerResult, literalResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [YulControl.caseArm, bind, markerResult]⟩

theorem yulCase_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 3)
    (error : ParserInvariantError) :
    YulControl.caseArm statement input ≠ .invariant error := by
  intro failed
  rcases yulCase_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

theorem yulCase_fuelElementTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel) :
    FuelElementTotalityContract (YulControl.caseArm statement)
      (statementFuel + 3) := {
  validFor := yulCase_weakValidFor statement statementContract.validFor
    statementContract.preservesTokenWindow
  preservesTokenWindow := yulCase_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  cursorLtOnSuccess := yulCase_cursor_lt_onSuccess statement
    statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := yulCase_ordinary_of_statementFuel statement statementFuel
    statementContract
}

/-- Loop fuel and recursive-statement fuel are independent in a case list. -/
theorem yulCases_ordinary_of_fuels
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel) :
    ∀ loopFuel casesRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < statementFuel + 3 →
      (∃ cases next,
        YulControl.caseList statement loopFuel casesRev input = .ok cases next) ∨
      (∃ failure next,
        YulControl.caseList statement loopFuel casesRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intros; omega
  | succ loopFuel inductionHypothesis =>
      intro casesRev input inputValid loopAdequate statementAdequate
      unfold YulControl.caseList
      split
      · let armContract := yulCase_fuelElementTotalityContract statement
          statementFuel statementContract
        cases armResult : YulControl.caseArm statement input with
        | invariant error =>
            exact False.elim (armContract.ne_invariant input inputValid
              statementAdequate error armResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok arm next =>
            have armReply := armContract.validFor input inputValid
            rw [armResult] at armReply
            have armWindow := armContract.preservesTokenWindow input
            rw [armResult] at armWindow
            have progress := armContract.cursorLtOnSuccess armResult
            have nextLoop : next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress armReply.2.1 armWindow.2
                progress loopAdequate
            have nextStatement : next.remainingCount < statementFuel + 3 :=
              remainingCount_lt_of_cursor_le armWindow.2
                (Nat.le_of_lt progress) statementAdequate
            change
              (∃ cases final,
                (if next.cursor > input.cursor then
                  YulControl.caseList statement loopFuel
                    (arm :: casesRev) next
                else
                  .invariant (.noProgress .yul next.currentSpan)) =
                    .ok cases final) ∨
              (∃ failure final,
                (if next.cursor > input.cursor then
                  YulControl.caseList statement loopFuel
                    (arm :: casesRev) next
                else
                  .invariant (.noProgress .yul next.currentSpan)) =
                    .reject failure final)
            rw [if_pos progress]
            exact inductionHypothesis (arm :: casesRev) next armReply.2.1
              nextLoop nextStatement
      · exact Or.inl ⟨casesRev.reverse, input, rfl⟩

theorem yulCases_ne_invariant_of_fuels
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (loopFuel : Nat) (casesRev : List YulCase)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (statementAdequate : input.remainingCount < statementFuel + 3)
    (error : ParserInvariantError) :
    YulControl.caseList statement loopFuel casesRev input ≠
      .invariant error := by
  intro failed
  rcases yulCases_ordinary_of_fuels statement statementFuel statementContract
      loopFuel casesRev input inputValid loopAdequate statementAdequate with
    ⟨cases, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Package the dynamically bounded case-list parser used by `switch`. -/
theorem yulCases_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelYulStatementTotalityContract statement statementFuel)
    (statementStrict : ∀ {input final : State} {value : YulStmt},
      statement input = .ok value final → input.cursor < final.cursor) :
    YulControl.FuelParserTotalityContract
      (fun input => YulControl.caseList statement
        (input.remainingCount + 1) [] input)
      (statementFuel + 3) := by
  let statementElement := statementContract.fuelElementTotalityContract
    statementStrict
  exact {
    validFor := fun input inputValid =>
      (yulCases_validFor statement statementContract.validFor
        statementContract.preservesTokens (input.remainingCount + 1)
          input inputValid).mono (fun _ _ _ => trivial)
    preservesTokenWindow := fun input =>
      yulCases_preservesTokenWindow statement
        statementContract.preservesTokenWindow
          (input.remainingCount + 1) [] input
    cursorMonotoneOnSuccess := fun input value next result =>
      yulCases_cursorMonotoneOnSuccess statement
        (input.remainingCount + 1) [] input value next result
    ordinary := fun input inputValid adequate =>
      yulCases_ordinary_of_fuels statement statementFuel statementElement
        (input.remainingCount + 1) [] input inputValid (by omega) adequate
  }

end Solcore.Syntax.Parser
