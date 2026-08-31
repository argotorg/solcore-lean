import Solcore.Syntax.Parser.ContractBodyProperties

/-! Token-window and cursor contracts for canonical contract bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

theorem closeContractBody_preservesTokenWindow (opening : Token)
    (membersRev : List ContractMember) :
    Parser.PreservesTokenWindow (closeContractBody opening membersRev) := by
  unfold closeContractBody
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBrace .topItem)
  intro closing
  exact Parser.pure_preservesTokenWindow _

theorem contractMembers_preservesTokenWindow (opening : Token) :
    ∀ fuel membersRev,
      Parser.PreservesTokenWindow (contractMembers opening fuel membersRev) := by
  intro fuel
  induction fuel with
  | zero => intros membersRev input; trivial
  | succ fuel inductionHypothesis =>
      intro membersRev input
      unfold contractMembers
      split
      · exact closeContractBody_preservesTokenWindow opening membersRev input
      · split
        · have shape := symbol_preservesTokenWindow .rightBrace .topItem input
          cases result : symbol .rightBrace .topItem input with
          | invariant error => trivial
          | ok closing next => trivial
          | reject failure rejected => rw [result] at shape; exact shape
        · have memberShape :=
            contractMemberWithAttribute_canonical_contract.preservesTokenWindow input
          cases memberResult : contractMemberWithAttribute input with
          | invariant error => trivial
          | ok member next =>
              rw [memberResult] at memberShape
              simp only
              split
              · exact (inductionHypothesis (member :: membersRev) next).trans
                  memberShape
              · trivial
          | reject failure failedState =>
              rw [memberResult] at memberShape
              dsimp only
              let rewound : State := { failedState with cursor := input.cursor }
              have rewoundShape : rewound.tokens = input.tokens ∧
                  rewound.window = input.window := by
                simpa [rewound, Reply.PreservesTokenWindow] using memberShape
              split
              · exact rewoundShape
              · have recoveryShape :=
                  recoverContractMember_preservesTokenWindow rewound
                cases recoveryResult : recoverContractMember rewound with
                | invariant error => trivial
                | reject failure rejected =>
                    rw [recoveryResult] at recoveryShape
                    exact recoveryShape.trans rewoundShape
                | ok member next =>
                    rw [recoveryResult] at recoveryShape
                    exact (inductionHypothesis (member :: membersRev) next).trans
                      (recoveryShape.trans rewoundShape)

theorem contractMembers_ok_state_shape (opening : Token) :
    ∀ fuel membersRev {input final : State} {body : ContractBody},
      contractMembers opening fuel membersRev input = .ok body final →
      input.cursor ≤ final.cursor ∧
        body.span.startByte = opening.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro membersRev input final body parsed
      unfold contractMembers at parsed
      split at parsed
      · unfold closeContractBody at parsed
        cases closingResult : symbol .rightBrace .topItem input with
        | invariant error =>
            simp only [bind, closingResult] at parsed
            contradiction
        | reject failure rejected =>
            simp only [bind, closingResult] at parsed
            contradiction
        | ok closing next =>
            have monotone := symbol_cursorMonotoneOnSuccess .rightBrace .topItem
              input closing next closingResult
            simp only [bind, closingResult, pure] at parsed
            cases parsed
            exact ⟨monotone, rfl⟩
      · split at parsed
        · cases closingResult : symbol .rightBrace .topItem input <;>
            simp [closingResult] at parsed
        · cases memberResult : contractMemberWithAttribute input with
          | invariant error => simp [memberResult] at parsed
          | ok member next =>
              simp only [memberResult] at parsed
              split at parsed
              · have recursive := inductionHypothesis (member :: membersRev) parsed
                exact ⟨Nat.le_trans (Nat.le_of_lt (by assumption)) recursive.1,
                  recursive.2⟩
              · contradiction
          | reject failure failedState =>
              simp only [memberResult] at parsed
              let rewound : State := { failedState with cursor := input.cursor }
              change (if atContractRecoveryBoundary input then
                  .reject failure rewound
                else match recoverContractMember rewound with
                  | .ok member next =>
                      contractMembers opening fuel (member :: membersRev) next
                  | .reject recoveryFailure next => .reject recoveryFailure next
                  | .invariant error => .invariant error) = .ok body final at parsed
              split at parsed
              · contradiction
              · cases recoveryResult : recoverContractMember rewound with
                | invariant error => simp [recoveryResult] at parsed
                | reject failure rejected => simp [recoveryResult] at parsed
                | ok member next =>
                    simp only [recoveryResult] at parsed
                    have recursive := inductionHypothesis (member :: membersRev) parsed
                    have progress : input.cursor < next.cursor := by
                      simpa [rewound] using
                        recoverContractMember_cursor_lt_onSuccess recoveryResult
                    exact ⟨Nat.le_trans (Nat.le_of_lt progress) recursive.1,
                      recursive.2⟩

theorem contractBody_preservesTokenWindow :
    Parser.PreservesTokenWindow contractBody := by
  intro input
  unfold contractBody
  have openingShape := symbol_preservesTokenWindow .leftBrace .topItem input
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => trivial
  | reject failure rejected => rw [openingResult] at openingShape; exact openingShape
  | ok opening next =>
      rw [openingResult] at openingShape
      exact (contractMembers_preservesTokenWindow opening
        (next.remainingCount + 1) [] next).trans openingShape

theorem contractBody_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess contractBody :=
  contractBody_preservesTokenWindow.preservesTokensOnSuccess

theorem contractBody_ok_state_shape {input final : State} {body : ContractBody}
    (parsed : contractBody input = .ok body final) :
    input.cursor < final.cursor ∧
      ∃ opening, input.peek? = some opening ∧
        opening.span.startByte = body.span.startByte := by
  unfold contractBody at parsed
  cases openingResult : symbol .leftBrace .topItem input with
  | invariant error => simp [openingResult] at parsed
  | reject failure rejected => simp [openingResult] at parsed
  | ok opening next =>
      simp only [openingResult] at parsed
      have shape := symbol_ok_state_shape .leftBrace .topItem openingResult
      have bodyShape := contractMembers_ok_state_shape opening
        (next.remainingCount + 1) [] parsed
      exact ⟨Nat.lt_of_lt_of_le (by simp [shape.2]) bodyShape.1,
        opening, shape.1, bodyShape.2.symm⟩

theorem contractBody_cursor_lt_onSuccess {input final : State}
    {body : ContractBody} (parsed : contractBody input = .ok body final) :
    input.cursor < final.cursor := (contractBody_ok_state_shape parsed).1

theorem contractBody_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess contractBody :=
  fun _ _ _ parsed => Nat.le_of_lt (contractBody_cursor_lt_onSuccess parsed)

theorem contractBody_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractBody (·.span) :=
  fun _ _ _ parsed => (contractBody_ok_state_shape parsed).2

end Solcore.Syntax.Parser.ContractInternals
