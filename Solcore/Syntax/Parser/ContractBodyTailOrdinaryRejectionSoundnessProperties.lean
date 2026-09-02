import Solcore.Syntax.Parser.ContractBodyOutcomePrimitiveProperties
import Solcore.Syntax.Parser.ContractMemberRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryOutcomeSoundnessProperties

/-! Broad ordinary-rejection soundness for contract-body member tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every rejecting fuel-bounded member loop records the exact first rejection
of its prioritized close, member, rewind, recovery, and recursive branches. -/
theorem contractMembers_reject_ordinaryOutcome_sound
    (opening : Token) :
    ∀ fuel membersRev input failure rejected,
      contractMembers opening fuel membersRev input =
        .reject failure rejected →
      DeclarativeGrammar.ContractMemberTailRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input failure rejected result
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input failure rejected result
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeContractBody_success_of_rightBrace_guard opening
              membersRev closingPresent with
            ⟨body, output, successful⟩
          rw [successful] at result
          contradiction
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          have closingAbsent :=
            symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              have atEnd : input.window.endIndex ≤ input.cursor := by
                simpa [State.atEnd] using ended
              cases closingResult : symbol .rightBrace .topItem input with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightBrace
                    .topItem closingResult
                  subst closingRejected
                  simp only [closingResult] at result
                  cases result
                  exact .windowEnd closingAbsent atEnd
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have inside := cursor_lt_endIndex_of_atEnd_eq_false ended
              cases memberResult : contractMemberWithAttribute input with
              | invariant error => simp [memberResult] at result
              | ok member afterMember =>
                  simp only [memberResult] at result
                  by_cases progress : afterMember.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    exact .laterDirect closingAbsent inside
                      (contractMemberWithAttribute_success_ordinaryOutcome_sound
                        memberResult)
                      progress
                      (inductionHypothesis (member :: membersRev) afterMember
                        failure rejected result)
                  · simp only [progress, if_false] at result
                    contradiction
              | reject memberFailure failedState =>
                  simp only [memberResult] at result
                  have memberRejected :=
                    contractMemberRejectsWithPreservedWindow_of_result
                      memberResult
                  have resultShape :=
                    contractMemberWithAttribute_canonical_contract
                      |>.preservesTokenWindow input
                  rw [memberResult] at resultShape
                  have shape : failedState.tokens = input.tokens ∧
                      failedState.window = input.window := by
                    simpa only [Reply.PreservesTokenWindow] using resultShape
                  let rewound : State := {
                    failedState with cursor := input.cursor
                  }
                  have rewoundEq : rewound.declarativeRemainder =
                      input.declarativeRemainder := by
                    dsimp only [rewound]
                    exact rewoundContractMember_declarativeRemainder_eq
                      input failedState shape
                  change (if atContractRecoveryBoundary input then
                      .reject memberFailure rewound
                    else match recoverContractMember rewound with
                      | .ok member afterRecovery =>
                          contractMembers opening fuel
                            (member :: membersRev) afterRecovery
                      | .reject recoveryFailure recoveryRejected =>
                          .reject recoveryFailure recoveryRejected
                      | .invariant error => .invariant error) =
                    .reject failure rejected at result
                  cases boundary : atContractRecoveryBoundary input with
                  | true =>
                      simp only [boundary, if_true] at result
                      have rejectedEq : rewound = rejected := by
                        injection result
                      rw [← rejectedEq, rewoundEq]
                      exact .memberAtBoundary closingAbsent inside
                        memberRejected
                        (contractMemberRecoveryBoundaryStartsAt_of_guard_eq_true
                          boundary)
                  | false =>
                      simp only [boundary, Bool.false_eq_true, if_false]
                        at result
                      have boundaryAbsent :=
                        no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
                          boundary
                      cases recoveryResult : recoverContractMember rewound with
                      | invariant error => simp [recoveryResult] at result
                      | reject recoveryFailure recoveryRejected =>
                          simp only [recoveryResult] at result
                          cases result
                          have recoveryGrammar :=
                            recoverContractMember_reject_ordinaryOutcome_sound
                              recoveryResult
                          rw [rewoundEq] at recoveryGrammar
                          exact .recoveryRejected closingAbsent inside
                            memberRejected boundaryAbsent recoveryGrammar
                      | ok member afterRecovery =>
                          simp only [recoveryResult] at result
                          have recoveryGrammar :=
                            recoverContractMember_success_ordinaryOutcome_sound
                              recoveryResult
                          rw [rewoundEq] at recoveryGrammar
                          exact .laterRecovered closingAbsent inside
                            memberRejected boundaryAbsent recoveryGrammar
                            (inductionHypothesis (member :: membersRev)
                              afterRecovery failure rejected result)

end Solcore.Syntax.Parser.ContractInternals
