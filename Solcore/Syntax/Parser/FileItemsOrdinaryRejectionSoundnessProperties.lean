import Solcore.Syntax.Parser.FileItemsOutcomePrimitiveProperties
import Solcore.Syntax.Parser.TopItemRecoveryOrdinaryOutcomeSoundnessProperties

/-! Broad ordinary-rejection soundness for source-file item accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every rejecting fuel-bounded file-item loop records the exact first
rejection of its prioritized end, item, rewind, boundary, recovery, and
recursive branches. -/
theorem parseItems_reject_ordinaryOutcome_sound :
    ∀ fuel itemsRev input failure rejected,
      parseItems fuel itemsRev input = .reject failure rejected →
      DeclarativeGrammar.FileItemsRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected result
      simp [parseItems] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input failure rejected result
      unfold parseItems at result
      cases ended : input.atEnd with
      | true => simp [ended] at result
      | false =>
          simp only [ended, Bool.false_eq_true, if_false] at result
          have inside := fileItemsCursor_lt_endIndex_of_atEnd_eq_false ended
          cases itemResult : parseItemsItem input with
          | invariant error => simp [itemResult] at result
          | ok item afterItem =>
              simp only [itemResult] at result
              by_cases progress : afterItem.cursor > input.cursor
              · simp only [progress, if_true] at result
                exact .laterDirect inside
                  (topItem_ordinaryOutcome_sound.1
                    (by simpa only [parseItemsItem] using itemResult))
                  progress
                  (inductionHypothesis (item :: itemsRev) afterItem failure
                    rejected result)
              · simp [progress] at result
          | reject itemFailure failedState =>
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
                    .ok itemsRev.reverse (rewound.emit itemFailure.toDiagnostic)
                  else match recoverTopItem rewound with
                    | .ok recovered afterRecovery =>
                        parseItems fuel (recovered :: itemsRev) afterRecovery
                    | .reject recoveryFailure recoveryRejected =>
                        .reject recoveryFailure recoveryRejected
                    | .invariant error => .invariant error) =
                .reject failure rejected at result
              cases boundary : atTopItemStart input with
              | true => simp [boundary] at result
              | false =>
                  simp only [boundary, Bool.false_eq_true, if_false] at result
                  have boundaryAbsent :=
                    no_fileItemsBoundaryStartsAt_of_guard_eq_false boundary
                  cases recoveryResult : recoverTopItem rewound with
                  | invariant error => simp [recoveryResult] at result
                  | reject recoveryFailure recoveryRejected =>
                      simp only [recoveryResult] at result
                      cases result
                      have recoveryGrammar :=
                        recoverTopItem_reject_ordinaryOutcome_sound
                          recoveryResult
                      rw [rewoundEq] at recoveryGrammar
                      exact .recoveryRejected inside itemRejected boundaryAbsent
                        recoveryGrammar
                  | ok recovered afterRecovery =>
                      simp only [recoveryResult] at result
                      have recoveryGrammar :=
                        recoverTopItem_success_ordinaryOutcome_sound
                          recoveryResult
                      rw [rewoundEq] at recoveryGrammar
                      exact .laterRecovered inside itemRejected boundaryAbsent
                        recoveryGrammar
                        (inductionHypothesis (recovered :: itemsRev)
                          afterRecovery failure rejected result)

end Solcore.Syntax.Parser.FileInternals
