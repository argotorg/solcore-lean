import Solcore.Syntax.DeclarativeContractMemberRecoveryExactnessProperties
import Solcore.Syntax.Parser.ContractMemberRecoveryBoundaryProperties
import Solcore.Syntax.Parser.ContractRecoveryTotalityProperties

/-! Exact executable ordinary outcomes for contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

/-- Every successful auxiliary recovery scan records its exact consumed token
sequence, stopping boundary, recovered span, AST, and final remainder. -/
theorem recoverContractMemberAux_success_ordinaryOutcome_sound
    (first : SourceSpan) :
    ∀ fuel last input member output,
      recoverContractMemberAux first last fuel input = .ok member output →
      DeclarativeGrammar.ContractMemberRecoveryScanParses first last
        input.declarativeRemainder member output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input member output result
      simp [recoverContractMemberAux] at result
  | succ fuel inductionHypothesis =>
      intro last input member output result
      unfold recoverContractMemberAux at result
      by_cases guard :
          (input.atEnd || atContractRecoveryBoundary input) = true
      · simp only [guard, if_true] at result
        unfold finishRecoveredMember at result
        cases result
        simpa [State.emit, State.declarativeRemainder,
          DeclarativeGrammar.recoveredContractMemberValue] using
          (DeclarativeGrammar.ContractMemberRecoveryScanParses.stop
            (first := first) (last := last)
            (contractMemberRecoveryStops_of_guard_eq_true input guard))
      · have guardFalse :
            (input.atEnd || atContractRecoveryBoundary input) = false :=
          Bool.eq_false_iff.mpr guard
        simp only [guardFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredMember at result
            cases result
            simpa [State.emit, State.declarativeRemainder,
              DeclarativeGrammar.recoveredContractMemberValue] using
              (DeclarativeGrammar.ContractMemberRecoveryScanParses.stop
                (first := first) (last := last)
                (contractMemberRecoveryStops_of_advance?_eq_none input
                  guardFalse advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next member output result
            rw [nextEq] at tail
            exact .next
              (no_contractMemberRecoveryStops_of_nonBoundary_token
                guardFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every executable recovery success consumes its mandatory first token and
then follows the exact boundary-preserving scan. -/
theorem recoverContractMember_success_ordinaryOutcome_sound
    {input output : State} {member : ContractMember}
    (result : recoverContractMember input = .ok member output) :
    DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder member output.declarativeRemainder := by
  unfold recoverContractMember at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases advance?_state_shape advanced with ⟨found, nextEq⟩
      have scan := recoverContractMemberAux_success_ordinaryOutcome_sound
        token.span (next.remainingCount + 1) token.span next member output result
      rw [nextEq] at scan
      exact .recovered (tokenAt_of_peek?_eq_some found) scan

/-- Every executable recovery rejection exactly records an unavailable
mandatory first token and retains the complete declarative remainder. -/
theorem recoverContractMember_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : recoverContractMember input = .reject failure rejected) :
    DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverContractMember at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      by_cases atEnd : input.window.endIndex ≤ input.cursor
      · exact .windowEnd atEnd
      · have inside : input.cursor < input.window.endIndex := by omega
        apply DeclarativeGrammar.ContractMemberRecoveryRejects.missingToken
          inside
        unfold State.advance? State.peek? at advanced
        simpa [State.declarativeRemainder, inside] using advanced
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverContractMemberAux_production_ok token.span token.span next
          with ⟨recovered, output, recoveredResult⟩
      rw [recoveredResult] at result
      contradiction

/-- Package standalone contract-member recovery success and rejection. -/
theorem recoverContractMember_ordinaryOutcome_sound :
    (∀ {input output : State} {member : ContractMember},
      recoverContractMember input = .ok member output →
        DeclarativeGrammar.ContractMemberRecoveryParses
          input.declarativeRemainder member output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverContractMember input = .reject failure rejected →
        DeclarativeGrammar.ContractMemberRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverContractMember_success_ordinaryOutcome_sound,
    recoverContractMember_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic standalone recovery outcomes. -/
theorem recoverContractMember_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberRecoveryParses
      DeclarativeGrammar.ContractMemberRecoveryRejects :=
  DeclarativeGrammar.contractMemberRecoveryDeterministicOutcomeSpec

/-- Re-export exact contract-member recovery functionality at the executable
boundary. -/
theorem recoverContractMember_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ContractMemberRecoveryParses
      DeclarativeGrammar.ContractMemberRecoveryRejects :=
  DeclarativeGrammar.contractMemberRecoveryExactOutcomeSpec

/-- Two successful recovery reflections have the same member AST and final
declarative remainder. -/
theorem recoverContractMember_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : ContractMember}
    (leftResult : recoverContractMember input = .ok left leftOutput)
    (rightResult : recoverContractMember input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberRecoveryParses.result_unique
    (recoverContractMember_success_ordinaryOutcome_sound leftResult)
    (recoverContractMember_success_ordinaryOutcome_sound rightResult)

/-- Two recovery rejections have the same exact declarative endpoint. -/
theorem recoverContractMember_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : recoverContractMember input =
      .reject leftFailure leftOutput)
    (rightResult : recoverContractMember input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.ContractMemberRecoveryRejects.output_unique
    (recoverContractMember_reject_ordinaryOutcome_sound leftResult)
    (recoverContractMember_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.ContractInternals
