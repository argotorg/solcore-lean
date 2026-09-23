import Solcore.Syntax.Parser.FileRecoveryProperties
import Solcore.Syntax.Parser.Trivia

/-! Source-validity contracts for complete-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

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

/-- The fuel-bounded file loop preserves accumulated item provenance.

The complete item parser's validity and token-window laws are explicit so the
declaration dispatcher can be proved independently.
-/
theorem parseItems_validFor
    (itemValid : parseItemsItem.ValidFor RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem) :
    ∀ fuel itemsRev input,
      input.ValidFor →
      List.ValidFor RecoveredTopItemValid input.file itemsRev →
      (parseItems fuel itemsRev input).ValidFor input
        (List.ValidFor RecoveredTopItemValid) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro itemsRev input inputValid itemsValid
      unfold parseItems
      split
      · refine ⟨?_, inputValid, rfl⟩
        intro item member
        exact itemsValid item (by simpa using member)
      · have itemReply := itemValid input inputValid
        have itemShape := itemWindow input
        cases itemResult : parseItemsItem input with
        | invariant error => trivial
        | ok item next =>
            rw [itemResult] at itemReply itemShape
            dsimp only
            split
            · have accumulated : List.ValidFor RecoveredTopItemValid
                  next.file (item :: itemsRev) := by
                intro retained member
                rcases List.mem_cons.mp member with rfl | priorMember
                · simpa [itemReply.2.2] using itemReply.1
                · simpa [itemReply.2.2] using
                    itemsValid retained priorMember
              exact (inductionHypothesis (item :: itemsRev) next
                itemReply.2.1 accumulated).of_file_eq itemReply.2.2
            · trivial
        | reject failure failedState =>
            rw [itemResult] at itemReply itemShape
            dsimp only
            let rewound : State := {
              failedState with cursor := input.cursor
            }
            have rewoundValid : rewound.ValidFor := by
              exact rewindAfterItemReject_validFor inputValid itemReply.2.1
                itemShape.2
            have rewoundFile : rewound.file = input.file := by
              simpa [rewound] using itemReply.2.2
            have failureValid : failure.span.ValidFor rewound.file := by
              simpa [rewound, itemReply.2.2] using itemReply.1
            split
            · refine ⟨?_, rewoundValid.emit_validFor failure.toDiagnostic
                  (failure.toDiagnostic_span_validFor failureValid), ?_⟩
              · intro retained member
                exact itemsValid retained (by simpa using member)
              · simpa [State.emit] using rewoundFile
            · have recoveryReply := recoverTopItem_validFor rewound rewoundValid
              cases recoveryResult : recoverTopItem rewound with
              | invariant error => trivial
              | reject recoveryFailure rejected =>
                  rw [recoveryResult] at recoveryReply
                  dsimp only
                  exact recoveryReply.of_file_eq rewoundFile
              | ok item next =>
                  rw [recoveryResult] at recoveryReply
                  dsimp only
                  have accumulated : List.ValidFor RecoveredTopItemValid
                      next.file (item :: itemsRev) := by
                    intro retained member
                    rcases List.mem_cons.mp member with rfl | priorMember
                    · simpa [recoveryReply.2.2] using recoveryReply.1
                    · simpa [recoveryReply.2.2, rewoundFile] using
                        itemsValid retained priorMember
                  exact (inductionHypothesis (item :: itemsRev) next
                    recoveryReply.2.1 accumulated).of_file_eq
                      (recoveryReply.2.2.trans rewoundFile)

/-- A complete-file reply constructs a fully source-valid canonical syntax file. -/
theorem sourceFile_reply_validFor
    (itemValid : parseItemsItem.ValidFor RecoveredTopItemValid)
    (itemWindow : Parser.PreservesTokenWindow parseItemsItem)
    {comments : List Comment} {input : State}
    (inputValid : input.ValidFor)
    (commentsValid : ∀ comment ∈ comments,
      comment.span.ValidFor input.file) :
    (sourceFile comments input).ValidFor input
      (ParsedFile.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor) := by
  have itemsReply := parseItems_validFor itemValid itemWindow
    (input.remainingCount + 1) [] input inputValid (by
      simp [List.ValidFor])
  unfold sourceFile
  cases itemsResult : parseItems (input.remainingCount + 1) [] input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [itemsResult] at itemsReply
      exact itemsReply
  | ok items next =>
      rw [itemsResult] at itemsReply
      exact ⟨parsedFile_withAttachedComments_validFor
          CoreStatement.ValidFor CoreExpr.ValidFor input.file comments
          commentsValid items itemsReply.1,
        itemsReply.2.1, itemsReply.2.2⟩

end Solcore.Syntax.Parser.FileInternals
