import Solcore.Syntax.Parser.ContractBodyOutcomePrimitiveProperties
import Solcore.Syntax.Parser.ContractMemberRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinarySuccessSoundnessProperties

/-! Broad ordinary-success soundness for contract-body member tails. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- Every successful fuel-bounded member loop exposes its exact closing brace,
new members in source order, and the corresponding broad ordinary tail. -/
theorem contractMembers_success_ordinaryOutcome_sound_strong
    (opening : Token) :
    ∀ fuel membersRev input body output,
      contractMembers opening fuel membersRev input = .ok body output →
      ∃ members closingSpan,
        body = {
          span := SourceSpan.cover opening.span closingSpan
          members := membersRev.reverse ++ members
        } ∧
        DeclarativeGrammar.ContractMemberTailOrdinaryParses
          input.declarativeRemainder members closingSpan
            output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input body output result
      simp [contractMembers] at result
  | succ fuel inductionHypothesis =>
      intro membersRev input body output result
      unfold contractMembers at result
      cases closingPresent : isSymbol input .rightBrace with
      | true =>
          simp only [closingPresent, if_true] at result
          rcases closeContractBody_success_exact opening membersRev result with
            ⟨closingSpan, bodyEq, closingParsed⟩
          exact ⟨[], closingSpan, by simpa using bodyEq,
            .close closingSpan closingParsed⟩
      | false =>
          simp only [closingPresent, Bool.false_eq_true, if_false] at result
          cases ended : input.atEnd with
          | true =>
              simp only [ended, if_true] at result
              cases closingResult : symbol .rightBrace .topItem input <;>
                simp [closingResult] at result
          | false =>
              simp only [ended, Bool.false_eq_true, if_false] at result
              have closingAbsent :=
                symbolAbsentAt_of_isSymbol_eq_false .rightBrace closingPresent
              have inside := cursor_lt_endIndex_of_atEnd_eq_false ended
              cases memberResult : contractMemberWithAttribute input with
              | invariant error => simp [memberResult] at result
              | ok member afterMember =>
                  simp only [memberResult] at result
                  by_cases progress : afterMember.cursor > input.cursor
                  · simp only [progress, if_true] at result
                    rcases inductionHypothesis (member :: membersRev)
                        afterMember body output result with
                      ⟨members, closingSpan, bodyEq, tailParsed⟩
                    refine ⟨member :: members, closingSpan, ?_,
                      .direct closingAbsent inside
                        (contractMemberWithAttribute_success_ordinaryOutcome_sound
                          memberResult)
                        progress tailParsed⟩
                    simpa [List.reverse_cons, List.append_assoc] using bodyEq
                  · simp only [progress, if_false] at result
                    contradiction
              | reject failure failedState =>
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
                      .reject failure rewound
                    else match recoverContractMember rewound with
                      | .ok member afterRecovery =>
                          contractMembers opening fuel
                            (member :: membersRev) afterRecovery
                      | .reject recoveryFailure rejected =>
                          .reject recoveryFailure rejected
                      | .invariant error => .invariant error) =
                    .ok body output at result
                  cases boundary : atContractRecoveryBoundary input with
                  | true => simp [boundary] at result
                  | false =>
                      simp only [boundary, Bool.false_eq_true, if_false]
                        at result
                      cases recoveryResult : recoverContractMember rewound with
                      | invariant error => simp [recoveryResult] at result
                      | reject recoveryFailure rejected =>
                          simp [recoveryResult] at result
                      | ok member afterRecovery =>
                          simp only [recoveryResult] at result
                          rcases inductionHypothesis (member :: membersRev)
                              afterRecovery body output result with
                            ⟨members, closingSpan, bodyEq, tailParsed⟩
                          have recoveryParsed :=
                            recoverContractMember_success_ordinaryOutcome_sound
                              recoveryResult
                          rw [rewoundEq] at recoveryParsed
                          refine ⟨member :: members, closingSpan, ?_,
                            .recovered closingAbsent inside memberRejected
                              (no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
                                boundary)
                              recoveryParsed tailParsed⟩
                          simpa [List.reverse_cons, List.append_assoc]
                            using bodyEq

end Solcore.Syntax.Parser.ContractInternals
