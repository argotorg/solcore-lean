import Solcore.Syntax.Parser.ContractBodyStateProperties
import Solcore.Syntax.Parser.ContractMemberStrictProperties
import Solcore.Syntax.Parser.ContractRecoveryTotalityProperties

/-! Conditional totality for canonical contract-body accumulation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- The one remaining invariant-freedom premise at the member boundary. -/
def ContractMemberInvariantFreeOnValid : Prop :=
  ∀ input, input.ValidFor → ∀ error,
    contractMemberWithAttribute input ≠ .invariant error

private theorem acceptToken_ordinary (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool) (state : State) :
    (∃ token final,
      acceptToken expected context accepts state = .ok token final) ∨
      (∃ failure final,
        acceptToken expected context accepts state = .reject failure final) := by
  cases result : acceptToken expected context accepts state with
  | ok token final => exact Or.inl ⟨token, final, rfl⟩
  | reject failure final => exact Or.inr ⟨failure, final, rfl⟩
  | invariant error =>
      unfold acceptToken at result
      cases found : state.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          simp only [found] at result
          split at result
          · contradiction
          · simp [rejectAt] at result

private theorem rewindAfterMemberReject_validFor
    {input failedState : State}
    (inputValid : input.ValidFor) (failedValid : failedState.ValidFor)
    (windowEq : failedState.window = input.window) :
    ({ failedState with cursor := input.cursor } : State).ValidFor := {
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
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

private theorem closeContractBody_ordinary (opening : Token)
    (membersRev : List ContractMember) (state : State) :
    (∃ body final,
      closeContractBody opening membersRev state = .ok body final) ∨
      (∃ failure final,
        closeContractBody opening membersRev state = .reject failure final) := by
  rcases acceptToken_ordinary (.symbol .rightBrace) .topItem
      (fun kind => kind == .symbol .rightBrace) state with success | rejection
  · rcases success with ⟨closing, next, closingResult⟩
    left
    unfold closeContractBody
    simp only [symbol, closingResult, bind, pure]
    exact ⟨_, _, rfl⟩
  · rcases rejection with ⟨failure, next, closingResult⟩
    right
    unfold closeContractBody
    simp only [symbol, closingResult, bind]
    exact ⟨failure, next, rfl⟩

/--
With an ordinary member parser and adequate fuel, contract accumulation has
only an ordinary success or rejection.  Its fuel and no-progress invariants
are therefore unreachable.
-/
theorem contractMembers_ordinary_of_remainingCount_lt
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (opening : Token) :
    ∀ fuel membersRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body final,
        contractMembers opening fuel membersRev input = .ok body final) ∨
        (∃ failure final,
          contractMembers opening fuel membersRev input =
            .reject failure final) := by
  intro fuel
  induction fuel with
  | zero =>
      intro membersRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro membersRev input inputValid adequate
      unfold contractMembers
      split
      · exact closeContractBody_ordinary opening membersRev input
      · rename_i notClosing
        split
        · rename_i atEnd
          have cursorAtEnd : input.window.endIndex ≤ input.cursor := by
            simpa [State.atEnd] using atEnd
          have peekNone : input.peek? = none := by
            unfold State.peek?
            simp [Nat.not_lt_of_ge cursorAtEnd]
          right
          simp [symbol, acceptToken, peekNone, rejectAt]
        · rename_i notAtEnd
          have memberReply :=
            contractMemberWithAttribute_canonical_contract.validFor
              input inputValid
          have memberWindow :=
            contractMemberWithAttribute_canonical_contract.preservesTokenWindow
              input
          cases memberResult : contractMemberWithAttribute input with
          | invariant error =>
              exact False.elim
                (memberInvariantFree input inputValid error memberResult)
          | ok member next =>
              rw [memberResult] at memberReply memberWindow
              have progress :=
                contractMemberWithAttribute_cursor_lt_onSuccess memberResult
              have nextAdequate := remainingCount_lt_after_strict_progress
                memberReply.2.1 memberWindow.2 progress adequate
              have recursive := inductionHypothesis (member :: membersRev)
                next memberReply.2.1 nextAdequate
              dsimp only
              split
              · exact recursive
              · omega
          | reject failure failedState =>
              rw [memberResult] at memberReply memberWindow
              let rewound : State := {
                failedState with cursor := input.cursor
              }
              have rewoundValid : rewound.ValidFor :=
                rewindAfterMemberReject_validFor inputValid memberReply.2.1
                  memberWindow.2
              have rewoundNotAtEnd : rewound.atEnd = false := by
                simpa [rewound, State.atEnd, memberWindow.2] using notAtEnd
              dsimp only
              split
              · right
                exact ⟨failure, rewound, rfl⟩
              · rcases recoverContractMember_ok_of_valid_not_atEnd
                    rewound rewoundValid rewoundNotAtEnd with
                  ⟨recovered, next, recoveryResult⟩
                have recoveryReply :=
                  recoverContractMember_validFor rewound rewoundValid
                rw [recoveryResult] at recoveryReply
                have recoveryWindow :=
                  recoverContractMember_preservesTokenWindow rewound
                rw [recoveryResult] at recoveryWindow
                have rewoundAdequate :
                    rewound.remainingCount < fuel + 1 := by
                  simpa only [State.remainingCount, rewound, memberWindow.2]
                    using adequate
                have nextAdequate := remainingCount_lt_after_strict_progress
                  recoveryReply.2.1 recoveryWindow.2
                  (recoverContractMember_cursor_lt_onSuccess recoveryResult)
                  rewoundAdequate
                have recursive := inductionHypothesis
                  (recovered :: membersRev) next recoveryReply.2.1
                  nextAdequate
                have recoveryResult' :
                    recoverContractMember {
                      failedState with cursor := input.cursor
                    } = .ok recovered next := by
                  simpa [rewound] using recoveryResult
                simpa only [recoveryResult'] using recursive

/-- The production loop fuel is adequate for every valid body state. -/
theorem contractMembers_production_ordinary
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (opening : Token) (membersRev : List ContractMember)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final,
      contractMembers opening (input.remainingCount + 1) membersRev input =
        .ok body final) ∨
      (∃ failure final,
        contractMembers opening (input.remainingCount + 1) membersRev input =
          .reject failure final) :=
  contractMembers_ordinary_of_remainingCount_lt memberInvariantFree opening
    (input.remainingCount + 1) membersRev input inputValid (by omega)

/-- A valid contract body has only an ordinary public parser result. -/
theorem contractBody_ordinary
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body final, contractBody input = .ok body final) ∨
      (∃ failure final, contractBody input = .reject failure final) := by
  rcases acceptToken_ordinary (.symbol .leftBrace) .topItem
      (fun kind => kind == .symbol .leftBrace) input with success | rejection
  · rcases success with ⟨opening, next, openingResult⟩
    have openingResult' : symbol .leftBrace .topItem input =
        .ok opening next := openingResult
    have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult'] at openingReply
    unfold contractBody
    simp only [openingResult']
    exact contractMembers_production_ordinary memberInvariantFree opening []
      next openingReply.2.1
  · rcases rejection with ⟨failure, next, openingResult⟩
    have openingResult' : symbol .leftBrace .topItem input =
        .reject failure next := openingResult
    right
    unfold contractBody
    simp only [openingResult']
    exact ⟨failure, next, rfl⟩

/-- The body parser cannot expose an invariant under the single member premise. -/
theorem contractBody_ne_invariant
    (memberInvariantFree : ContractMemberInvariantFreeOnValid)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractBody input ≠ .invariant error := by
  intro failed
  rcases contractBody_ordinary memberInvariantFree input inputValid with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ContractInternals
