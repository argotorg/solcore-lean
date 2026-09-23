import Solcore.Syntax.Parser.FileItemsProperties

/-! State-transition laws for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The fuel-bounded item loop retains its immutable token window. -/
theorem parseItems_preservesTokenWindow
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem) :
    ∀ fuel itemsRev,
      Parser.PreservesTokenWindow (parseItems fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro itemsRev input
      unfold parseItems
      split
      · exact ⟨rfl, rfl⟩
      · have itemShape := itemWindow input
        cases itemResult : parseItemsItem input with
        | invariant error => trivial
        | ok item next =>
            rw [itemResult] at itemShape
            dsimp only
            split
            · exact (inductionHypothesis (item :: itemsRev) next).trans
                itemShape
            · trivial
        | reject failure failedState =>
            rw [itemResult] at itemShape
            dsimp only
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            have rewoundShape : rewound.tokens = input.tokens ∧
                rewound.window = input.window := by
              exact itemShape
            split
            · exact ⟨rewoundShape.1, rewoundShape.2⟩
            · have recoveryShape :=
                recoverTopItem_preservesTokenWindow rewound
              cases recoveryResult : recoverTopItem rewound with
              | invariant error => trivial
              | reject recoveryFailure rejected =>
                  rw [recoveryResult] at recoveryShape
                  dsimp only
                  exact recoveryShape.trans rewoundShape
              | ok recovered next =>
                  rw [recoveryResult] at recoveryShape
                  dsimp only
                  exact (inductionHypothesis (recovered :: itemsRev) next).trans
                    (recoveryShape.trans rewoundShape)

/-- The file loop retains its token carrier on every successful result. -/
theorem parseItems_preservesTokensOnSuccess
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    (fuel : Nat) (itemsRev : List TopItem) :
    Parser.PreservesTokensOnSuccess (parseItems fuel itemsRev) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (parseItems_preservesTokenWindow itemWindow fuel itemsRev)

/-- Successful item accumulation never moves the cursor backwards. -/
theorem parseItems_cursorMonotoneOnSuccess
    (itemCursor : Parser.CursorMonotoneOnSuccess parseItemsItem) :
    ∀ fuel itemsRev,
      Parser.CursorMonotoneOnSuccess (parseItems fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items final parsed
      simp [parseItems] at parsed
  | succ fuel inductionHypothesis =>
      intro itemsRev input items final parsed
      unfold parseItems at parsed
      split at parsed
      · cases parsed
        exact Nat.le_refl _
      · cases itemResult : parseItemsItem input with
        | invariant error => simp [itemResult] at parsed
        | ok item next =>
            simp only [itemResult] at parsed
            split at parsed
            · exact Nat.le_trans (itemCursor input item next itemResult)
                (inductionHypothesis (item :: itemsRev) next items final parsed)
            · simp at parsed
        | reject failure failedState =>
            simp only [itemResult] at parsed
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            split at parsed
            · cases parsed
              exact Nat.le_refl _
            · change (match recoverTopItem rewound with
                | .ok recovered next =>
                    parseItems fuel (recovered :: itemsRev) next
                | .reject recoveryFailure rejected =>
                    .reject recoveryFailure rejected
                | .invariant error => .invariant error) =
                  .ok items final at parsed
              cases recoveryResult : recoverTopItem rewound with
              | invariant error =>
                  rw [recoveryResult] at parsed
                  cases parsed
              | reject recoveryFailure rejected =>
                  rw [recoveryResult] at parsed
                  cases parsed
              | ok recovered next =>
                  rw [recoveryResult] at parsed
                  exact Nat.le_trans
                    (recoverTopItem_cursorMonotoneOnSuccess rewound
                      recovered next recoveryResult)
                    (inductionHypothesis (recovered :: itemsRev) next items
                      final parsed)

/-- Complete-file parsing preserves the immutable token window. -/
theorem sourceFile_preservesTokenWindow
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    (comments : List Comment) :
    Parser.PreservesTokenWindow (sourceFile comments) := by
  intro input
  unfold sourceFile
  have itemsShape := parseItems_preservesTokenWindow itemWindow
    (input.remainingCount + 1) [] input
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [itemsResult] at itemsShape
      exact itemsShape
  | ok items next =>
      rw [itemsResult] at itemsShape
      exact itemsShape

/-- Complete-file parsing retains the token carrier on success. -/
theorem sourceFile_preservesTokensOnSuccess
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    (comments : List Comment) :
    Parser.PreservesTokensOnSuccess (sourceFile comments) :=
  Parser.PreservesTokenWindow.preservesTokensOnSuccess
    (sourceFile_preservesTokenWindow itemWindow comments)

/-- Complete-file parsing never moves the cursor backwards on success. -/
theorem sourceFile_cursorMonotoneOnSuccess
    (itemCursor : Parser.CursorMonotoneOnSuccess parseItemsItem)
    (comments : List Comment) :
    Parser.CursorMonotoneOnSuccess (sourceFile comments) := by
  intro input parsedFile next parsed
  unfold sourceFile at parsed
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error =>
      rw [itemsResult] at parsed
      cases parsed
  | reject failure rejected =>
      rw [itemsResult] at parsed
      cases parsed
  | ok items final =>
      simp only [itemsResult] at parsed
      have monotone : input.cursor ≤ final.cursor :=
        parseItems_cursorMonotoneOnSuccess itemCursor
          (input.remainingCount + 1) [] input items final itemsResult
      cases parsed
      exact monotone

end Solcore.Syntax.Parser.FileInternals
