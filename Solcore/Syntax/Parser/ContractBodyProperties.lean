import Solcore.Syntax.Parser.ContractProperties
import Solcore.Syntax.Parser.ContractRecoveryProperties

/-! Contracts for canonical contract-body accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

namespace ContractBody

def ValidFor (file : SourceFile) (body : ContractBody) : Prop :=
  body.span.ValidFor file ∧
    List.ValidFor CanonicalContractMemberValid file body.members

end ContractBody

private theorem rewindAfterMemberReject_validFor {input failedState : State}
    (inputValid : input.ValidFor) (failedValid : failedState.ValidFor)
    (windowEq : failedState.window = input.window) :
    ({ failedState with cursor := input.cursor } : State).ValidFor := {
  tokens := failedValid.tokens
  cursor_le_endIndex := by simpa [windowEq] using inputValid.cursor_le_endIndex
  endIndex_le_size := failedValid.endIndex_le_size
  endByte_le_source := failedValid.endByte_le_source
  endByte_boundary := failedValid.endByte_boundary
  diagnosticsRev := failedValid.diagnosticsRev
}

theorem closeContractBody_validFor (opening : Token)
    (membersRev : List ContractMember) (input : State) (openingIndex : Nat)
    (inputValid : input.ValidFor)
    (openingFound : input.tokens[openingIndex]? = some opening)
    (openingBefore : openingIndex < input.cursor)
    (membersValid : List.ValidFor CanonicalContractMemberValid
      input.file membersRev) :
    (closeContractBody opening membersRev input).ValidFor input
      ContractBody.ValidFor := by
  unfold closeContractBody
  have closingReply := symbol_validFor .rightBrace .topItem input inputValid
  cases closingResult : symbol .rightBrace .topItem input with
  | invariant error => simp only [bind, closingResult]; trivial
  | reject failure rejected =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult]
      exact closingReply
  | ok closing next =>
      rw [closingResult] at closingReply
      simp only [bind, closingResult, pure, Reply.ValidFor]
      have closingShape := symbol_ok_state_shape .rightBrace .topItem closingResult
      have closingAt := State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have openingValid :=
        inputValid.token_span_validFor_of_getElem?_eq_some openingFound
      have closingValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using closingReply.1
      have separated := inputValid.token_end_le_token_start_of_getElem?_lt
        openingFound closingAt openingBefore
      have bodyValid := SourceSpan.cover_validFor openingValid closingValid
        (Nat.le_trans openingValid.2.1
          (Nat.le_trans separated closingValid.2.1))
      refine ⟨⟨bodyValid, ?_⟩, closingReply.2.1, closingReply.2.2⟩
      intro member memberOf
      exact membersValid member (by simpa using memberOf)

theorem contractMembers_validFor (opening : Token) :
    ∀ fuel membersRev input openingIndex,
      input.ValidFor → input.tokens[openingIndex]? = some opening →
      openingIndex < input.cursor →
      List.ValidFor CanonicalContractMemberValid input.file membersRev →
      (contractMembers opening fuel membersRev input).ValidFor input
        ContractBody.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro membersRev input openingIndex inputValid openingFound openingBefore
        membersValid
      unfold contractMembers
      split
      · exact closeContractBody_validFor opening membersRev input openingIndex
          inputValid openingFound openingBefore membersValid
      · split
        · have closingReply := symbol_validFor .rightBrace .topItem input inputValid
          cases closingResult : symbol .rightBrace .topItem input with
          | invariant error => trivial
          | ok closing next => trivial
          | reject failure rejected =>
              rw [closingResult] at closingReply
              exact closingReply
        · have memberReply :=
            contractMemberWithAttribute_canonical_contract.validFor input inputValid
          have memberWindow :=
            contractMemberWithAttribute_canonical_contract.preservesTokenWindow input
          cases memberResult : contractMemberWithAttribute input with
          | invariant error => trivial
          | ok member next =>
              rw [memberResult] at memberReply memberWindow
              simp only
              split
              · have accumulated : List.ValidFor CanonicalContractMemberValid
                    next.file (member :: membersRev) := by
                  intro retained memberOf
                  rcases List.mem_cons.mp memberOf with rfl | prior
                  · simpa [memberReply.2.2] using memberReply.1
                  · simpa [memberReply.2.2] using membersValid retained prior
                have openingFoundNext : next.tokens[openingIndex]? = some opening := by
                  simpa [memberWindow.1] using openingFound
                exact (inductionHypothesis (member :: membersRev) next
                  openingIndex memberReply.2.1 openingFoundNext
                  (Nat.lt_trans openingBefore (by omega)) accumulated).of_file_eq
                    memberReply.2.2
              · trivial
          | reject failure failedState =>
              rw [memberResult] at memberReply memberWindow
              dsimp only
              let rewound : State := { failedState with cursor := input.cursor }
              have rewoundValid := rewindAfterMemberReject_validFor inputValid
                memberReply.2.1 memberWindow.2
              have rewoundFile : rewound.file = input.file := by
                simpa [rewound] using memberReply.2.2
              split
              · exact ⟨by simpa [rewound, memberReply.2.2] using memberReply.1,
                  rewoundValid, rewoundFile⟩
              · have recoveryReply := recoverContractMember_validFor
                  rewound rewoundValid
                cases recoveryResult : recoverContractMember rewound with
                | invariant error => trivial
                | reject recoveryFailure rejected =>
                    rw [recoveryResult] at recoveryReply
                    exact recoveryReply.of_file_eq rewoundFile
                | ok member next =>
                    rw [recoveryResult] at recoveryReply
                    have openingFoundNext : next.tokens[openingIndex]? =
                        some opening := by
                      simpa [recoverContractMember_preservesTokensOnSuccess
                        rewound member next recoveryResult, rewound,
                        memberWindow.1]
                        using openingFound
                    have accumulated : List.ValidFor
                        CanonicalContractMemberValid next.file
                        (member :: membersRev) := by
                      intro retained memberOf
                      rcases List.mem_cons.mp memberOf with rfl | prior
                      · simpa [recoveryReply.2.2] using recoveryReply.1
                      · simpa [recoveryReply.2.2, rewoundFile] using
                          membersValid retained prior
                    have progress : input.cursor < next.cursor := by
                      simpa [rewound] using
                        recoverContractMember_cursor_lt_onSuccess recoveryResult
                    exact (inductionHypothesis (member :: membersRev) next
                      openingIndex recoveryReply.2.1 openingFoundNext
                      (Nat.lt_trans openingBefore progress) accumulated
                        ).of_file_eq (recoveryReply.2.2.trans rewoundFile)

theorem contractBody_validFor : contractBody.ValidFor ContractBody.ValidFor := by
  intro input inputValid
  unfold contractBody
  have openingReply := symbol_validFor .leftBrace .topItem input inputValid
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected => rw [openingResult] at openingReply; exact openingReply
  | ok opening next =>
      rw [openingResult] at openingReply
      have shape := symbol_ok_state_shape .leftBrace .topItem openingResult
      have openingAt := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (contractMembers_validFor opening (next.remainingCount + 1) [] next
        input.cursor openingReply.2.1 (by simpa [shape.2] using openingAt)
        (by simp [shape.2]) (by simp [List.ValidFor])).of_file_eq
          openingReply.2.2

end Solcore.Syntax.Parser.ContractInternals
