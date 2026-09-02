import Solcore.Syntax.DeclarativeFileItemsOutcomeGrammar
import Solcore.Syntax.Parser.FileCompleteProperties
import Solcore.Syntax.Parser.TopItemOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TopItemRecoveryBoundaryProperties

/-! Shared executable primitives for broad source-file item-loop outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- A complete top-item rejection and its canonical state contract supply the
declarative rewind witness used by the file loop. -/
theorem topItemRejectsWithPreservedWindow_of_result
    {input failed : State} {failure : Failure}
    (result : parseItemsItem input = .reject failure failed) :
    DeclarativeGrammar.TopItemRejectsWithPreservedWindow
      input.declarativeRemainder := by
  have resultShape := parseItemsItem_complete_contract.preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧
      failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    topItem_reject_ordinaryOutcome_sound
      (by simpa only [parseItemsItem] using result),
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Preserved carrier and active window make the file-loop cursor rewind
declaratively invisible. -/
theorem rewoundTopItem_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

/-- A false executable end guard is exactly strict containment in the active
token window. -/
theorem fileItemsCursor_lt_endIndex_of_atEnd_eq_false {input : State}
    (notAtEnd : input.atEnd = false) :
    input.cursor < input.window.endIndex := by
  unfold State.atEnd at notAtEnd
  have outside : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    rw [decide_eq_true atEnd] at notAtEnd
    contradiction
  omega

/-- A true executable boundary guard exposes the exact top-item boundary. -/
theorem fileItemsBoundaryStartsAt_of_guard_eq_true {input : State}
    (present : atTopItemStart input = true) :
    DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder :=
  importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true present

/-- A false executable boundary guard excludes every exact top-item
boundary. -/
theorem no_fileItemsBoundaryStartsAt_of_guard_eq_false {input : State}
    (absent : atTopItemStart input = false) :
    ¬ DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder := by
  intro starts
  have present := atTopItemStart_eq_true_of_topItemRecoveryBoundary starts
  rw [present] at absent
  contradiction

end Solcore.Syntax.Parser.FileInternals
