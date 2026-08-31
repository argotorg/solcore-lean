import Solcore.Syntax.Parser.Yul.ControlSwitchFuelTotalityProperties

/-! Fuel-aware totality for the optional default arm of a Yul switch. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem optionalYulDefault_weakValidFor
    (statement : Parser YulStmt)
    (statementValid : statement.ValidFor (fun _ _ => True))
    (statementWindow : Parser.PreservesTokenWindow statement) :
    (YulControl.optionalDefault statement).ValidFor (fun _ _ => True) := by
  unfold YulControl.optionalDefault
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · apply Parser.bind_validFor (keyword_validFor .defaultKw .yulStatement)
    intro marker
    apply Parser.bind_validFor
      (yulBlock_validFor (fun _ _ => True) statement statementValid
        statementWindow.preservesTokensOnSuccess)
    intro body
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  · exact Parser.pure_validFor none _ (fun _ => trivial)

/-- A present `default` spends one keyword unit before its block wrapper. -/
theorem optionalYulDefault_ordinary_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2) :
    (∃ value next,
      YulControl.optionalDefault statement input = .ok value next) ∨
    (∃ failure next,
      YulControl.optionalDefault statement input = .reject failure next) := by
  unfold YulControl.optionalDefault
  simp only [getState, bind]
  split
  · rcases (keyword_ordinary .defaultKw .yulStatement) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerReply := keyword_validFor .defaultKw .yulStatement input
        inputValid
      rw [markerResult] at markerReply
      have markerWindow := keyword_preservesTokenWindow .defaultKw
        .yulStatement input
      rw [markerResult] at markerWindow
      have bodyBudget : afterMarker.remainingCount < statementFuel + 1 :=
        remainingCount_lt_after_strict_progress markerReply.2.1 markerWindow.2
          (acceptToken_cursor_lt_onSuccess (.keyword .defaultKw)
            .yulStatement (· == .keyword .defaultKw) markerResult) adequate
      rcases (yulBlock_fuelElementTotalityContract statement statementFuel
          statementContract).ordinary afterMarker markerReply.2.1 bodyBudget with
        ⟨body, final, bodyResult⟩ | ⟨failure, rejected, bodyResult⟩
      · exact Or.inl ⟨some body, final, by
          simp only [markerResult, bodyResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [markerResult, bodyResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [markerResult]⟩
  · exact Or.inl ⟨none, input, rfl⟩

theorem optionalYulDefault_ne_invariant_of_statementFuel
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 2)
    (error : ParserInvariantError) :
    YulControl.optionalDefault statement input ≠ .invariant error := by
  intro failed
  rcases optionalYulDefault_ordinary_of_statementFuel statement statementFuel
      statementContract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Package the optional, potentially non-consuming default helper. -/
theorem optionalYulDefault_fuelTotalityContract
    (statement : Parser YulStmt) (statementFuel : Nat)
    (statementContract : FuelElementTotalityContract statement statementFuel) :
    YulControl.FuelParserTotalityContract
      (YulControl.optionalDefault statement) (statementFuel + 2) := {
  validFor := optionalYulDefault_weakValidFor statement
    statementContract.validFor statementContract.preservesTokenWindow
  preservesTokenWindow := optionalYulDefault_preservesTokenWindow statement
    statementContract.preservesTokenWindow
  cursorMonotoneOnSuccess := optionalYulDefault_cursorMonotoneOnSuccess
    statement statementContract.preservesTokenWindow.preservesTokensOnSuccess
  ordinary := optionalYulDefault_ordinary_of_statementFuel statement
    statementFuel statementContract
}

end Solcore.Syntax.Parser
