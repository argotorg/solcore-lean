import Solcore.Syntax.Parser.FileItemsOutcomePrimitiveProperties
import Solcore.Syntax.Parser.TopItemRecoveryOrdinaryOutcomeSoundnessProperties

/-! Broad ordinary-success reflection for the source-file item loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every successful fuel-bounded file-item loop exposes the forward suffix
added after its executable reverse accumulator and its exact broad outcome. -/
theorem parseItems_success_ordinaryOutcome_sound_strong :
    ∀ fuel itemsRev input items output,
      parseItems fuel itemsRev input = .ok items output →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.FileItemsOrdinaryParses
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output result
      simp [parseItems] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items output result
      unfold parseItems at result
      cases ended : input.atEnd with
      | true =>
          simp only [ended, if_true] at result
          cases result
          refine ⟨[], by simp, .done ?_⟩
          simpa [State.atEnd, State.declarativeRemainder] using ended
      | false =>
          simp only [ended, Bool.false_eq_true, if_false] at result
          have inside := fileItemsCursor_lt_endIndex_of_atEnd_eq_false ended
          cases itemResult : parseItemsItem input with
          | invariant error => simp [itemResult] at result
          | ok item afterItem =>
              simp only [itemResult] at result
              by_cases progress : afterItem.cursor > input.cursor
              · simp only [progress, if_true] at result
                rcases inductionHypothesis (item :: itemsRev) afterItem items
                    output result with
                  ⟨suffix, itemsEq, tailParsed⟩
                have itemParsed := topItem_success_ordinaryOutcome_sound
                  (by simpa only [parseItemsItem] using itemResult)
                have declarativeProgress :
                    input.declarativeRemainder.cursor <
                      afterItem.declarativeRemainder.cursor := by
                  simpa [State.declarativeRemainder] using progress
                refine ⟨item :: suffix, ?_, .direct inside itemParsed
                  declarativeProgress tailParsed⟩
                · simpa [List.reverse_cons, List.append_assoc] using itemsEq
              · simp only [progress, if_false] at result
                contradiction
          | reject failure failedState =>
              simp only [itemResult] at result
              have itemRejected :=
                topItemRejectsWithPreservedWindow_of_result itemResult
              have resultShape :=
                parseItemsItem_complete_contract.preservesTokenWindow input
              rw [itemResult] at resultShape
              have shape : failedState.tokens = input.tokens ∧
                  failedState.window = input.window := by
                simpa only [Reply.PreservesTokenWindow] using resultShape
              let rewound : State := {
                failedState with cursor := input.cursor
              }
              have rewoundEq : rewound.declarativeRemainder =
                  input.declarativeRemainder := by
                dsimp only [rewound]
                exact rewoundTopItem_declarativeRemainder_eq input failedState
                  shape
              change (if atTopItemStart input then
                  .ok itemsRev.reverse (rewound.emit failure.toDiagnostic)
                else match recoverTopItem rewound with
                  | .ok recovered next =>
                      parseItems fuel (recovered :: itemsRev) next
                  | .reject recoveryFailure rejected =>
                      .reject recoveryFailure rejected
                  | .invariant error => .invariant error) =
                .ok items output at result
              cases boundary : atTopItemStart input with
              | true =>
                  simp only [boundary, if_true] at result
                  cases result
                  refine ⟨[], by simp, ?_⟩
                  have outputEq :
                      (rewound.emit failure.toDiagnostic).declarativeRemainder =
                        input.declarativeRemainder := by
                    simpa [State.emit, State.declarativeRemainder] using
                      rewoundEq
                  rw [outputEq]
                  exact .boundaryStop inside itemRejected
                    (fileItemsBoundaryStartsAt_of_guard_eq_true boundary)
              | false =>
                  simp only [boundary, Bool.false_eq_true, if_false] at result
                  cases recoveryResult : recoverTopItem rewound with
                  | invariant error => simp [recoveryResult] at result
                  | reject recoveryFailure rejected =>
                      simp [recoveryResult] at result
                  | ok recovered afterRecovery =>
                      simp only [recoveryResult] at result
                      rcases inductionHypothesis (recovered :: itemsRev)
                          afterRecovery items output result with
                        ⟨suffix, itemsEq, tailParsed⟩
                      have recoveryParsed :=
                        recoverTopItem_success_ordinaryOutcome_sound
                          recoveryResult
                      rw [rewoundEq] at recoveryParsed
                      refine ⟨recovered :: suffix, ?_,
                        .recovered inside itemRejected
                          (no_fileItemsBoundaryStartsAt_of_guard_eq_false
                            boundary)
                          recoveryParsed tailParsed⟩
                      simpa [List.reverse_cons, List.append_assoc]
                        using itemsEq

end Solcore.Syntax.Parser.FileInternals
