import Solcore.Syntax.Parser.FileItemStrictProperties
import Solcore.Syntax.Parser.FileRecoveryTotalityProperties

/-! Conditional totality for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- The one remaining totality premise at the complete-item boundary. -/
def ParseItemsItemInvariantFree : Prop :=
  ∀ input, input.ValidFor → ∀ error,
    parseItemsItem input ≠ .invariant error

private theorem rewindAfterItemReject_validFor
    {input failedState : State}
    (inputValid : input.ValidFor) (failedValid : failedState.ValidFor)
    (windowEq : failedState.window = input.window) :
    ({ failedState with cursor := input.cursor } : State).ValidFor := by
  exact {
    tokens := failedValid.tokens
    cursor_le_endIndex := by
      simpa [windowEq] using inputValid.cursor_le_endIndex
    endIndex_le_size := failedValid.endIndex_le_size
    endByte_le_source := failedValid.endByte_le_source
    endByte_boundary := failedValid.endByte_boundary
    diagnosticsRev := failedValid.diagnosticsRev
  }

private theorem remainingCount_lt_after_strict_progress
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor)
    (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  simp only [State.remainingCount] at adequate ⊢
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  rw [endIndexEq]
  omega

/--
If complete-item parsing itself cannot expose an invariant, more fuel than
remaining tokens makes the complete-file loop return successfully.  Thus both
loop fuel exhaustion and its no-progress check are unreachable.
-/
theorem parseItems_exists_ok_of_remainingCount_lt
    (itemInvariantFree : ParseItemsItemInvariantFree) :
    ∀ fuel itemsRev input,
      input.ValidFor → input.remainingCount < fuel →
      ∃ items final, parseItems fuel itemsRev input = .ok items final := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro itemsRev input inputValid adequate
      unfold parseItems
      split
      · exact ⟨_, _, rfl⟩
      · rename_i notAtEnd
        have itemReply := parseItemsItem_complete_validFor input inputValid
        have itemWindow :=
          parseItemsItem_complete_contract.preservesTokenWindow input
        cases itemResult : parseItemsItem input with
        | invariant error =>
            exact False.elim
              (itemInvariantFree input inputValid error itemResult)
        | ok item next =>
            rw [itemResult] at itemReply itemWindow
            have progress := parseItemsItem_cursor_lt_onSuccess itemResult
            have nextAdequate := remainingCount_lt_after_strict_progress
              itemReply.2.1 itemWindow.2 progress adequate
            have recursive := inductionHypothesis (item :: itemsRev) next
              itemReply.2.1 nextAdequate
            dsimp only
            split
            · exact recursive
            · omega
        | reject failure failedState =>
            rw [itemResult] at itemReply itemWindow
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            have rewoundValid : rewound.ValidFor :=
              rewindAfterItemReject_validFor inputValid itemReply.2.1
                itemWindow.2
            have rewoundNotAtEnd : rewound.atEnd = false := by
              simpa [rewound, State.atEnd, itemWindow.2] using notAtEnd
            dsimp only
            split
            · exact ⟨_, _, rfl⟩
            · rcases recoverTopItem_exists_ok_of_validFor_not_atEnd
                  rewound rewoundValid rewoundNotAtEnd with
                ⟨recovered, next, recoveryResult, progress⟩
              have recoveryReply := recoverTopItem_validFor rewound rewoundValid
              rw [recoveryResult] at recoveryReply
              have recoveryWindow :=
                recoverTopItem_preservesTokenWindow rewound
              rw [recoveryResult] at recoveryWindow
              have rewoundAdequate :
                  rewound.remainingCount < fuel + 1 := by
                simpa only [State.remainingCount, rewound, itemWindow.2]
                  using adequate
              have nextAdequate := remainingCount_lt_after_strict_progress
                recoveryReply.2.1 recoveryWindow.2 progress
                rewoundAdequate
              have recursive := inductionHypothesis
                (recovered :: itemsRev) next recoveryReply.2.1 nextAdequate
              change ∃ items final,
                (match recoverTopItem rewound with
                | .ok recovered next =>
                    parseItems fuel (recovered :: itemsRev) next
                | .reject recoveryFailure rejected =>
                    .reject recoveryFailure rejected
                | .invariant error => .invariant error) = .ok items final
              simpa only [recoveryResult] using recursive

/-- The production fuel selected by the file parser always suffices. -/
theorem parseItems_production_exists_ok
    (itemInvariantFree : ParseItemsItemInvariantFree)
    (itemsRev : List TopItem) (input : State) (inputValid : input.ValidFor) :
    ∃ items final,
      parseItems (input.remainingCount + 1) itemsRev input = .ok items final :=
  parseItems_exists_ok_of_remainingCount_lt itemInvariantFree
    (input.remainingCount + 1) itemsRev input inputValid (by omega)

/-- A complete source-file parse succeeds under the single item premise. -/
theorem sourceFile_exists_ok
    (itemInvariantFree : ParseItemsItemInvariantFree)
    (comments : List Comment) (input : State) (inputValid : input.ValidFor) :
    ∃ parsed final, sourceFile comments input = .ok parsed final := by
  rcases parseItems_production_exists_ok itemInvariantFree [] input inputValid
      with ⟨items, final, parsedItems⟩
  unfold sourceFile
  simp only [parsedItems]
  exact ⟨_, _, rfl⟩

end Solcore.Syntax.Parser.FileInternals
