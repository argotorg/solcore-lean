import Solcore.Syntax.DeclarativeTopItemRecoveryExactnessProperties
import Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeProperties
import Solcore.Syntax.Parser.FileRecoveryTotalityProperties
import Solcore.Syntax.Parser.TopItemRecoveryBoundaryProperties

/-! Exact executable ordinary outcomes for top-item recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

private theorem recoveryAdvance_state_shape {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
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
theorem recoverTopItemAux_success_ordinaryOutcome_sound
    (first : SourceSpan) :
    ∀ fuel last input item output,
      recoverTopItemAux first last fuel input = .ok item output →
      DeclarativeGrammar.TopItemRecoveryScanParses first last
        input.declarativeRemainder item output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input item output result
      simp [recoverTopItemAux] at result
  | succ fuel inductionHypothesis =>
      intro last input item output result
      unfold recoverTopItemAux at result
      by_cases guard : (input.atEnd || atTopItemStart input) = true
      · simp only [guard, if_true] at result
        unfold finishRecoveredTopItem at result
        cases result
        simpa [State.emit, State.declarativeRemainder,
          DeclarativeGrammar.recoveredTopItemValue] using
          (DeclarativeGrammar.TopItemRecoveryScanParses.stop
            (first := first) (last := last)
            (topItemRecoveryStops_of_guard_eq_true input guard))
      · have guardFalse :
            (input.atEnd || atTopItemStart input) = false :=
          Bool.eq_false_iff.mpr guard
        simp only [guardFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredTopItem at result
            cases result
            simpa [State.emit, State.declarativeRemainder,
              DeclarativeGrammar.recoveredTopItemValue] using
              (DeclarativeGrammar.TopItemRecoveryScanParses.stop
                (first := first) (last := last)
                (topItemRecoveryStops_of_advance?_eq_none input guardFalse
                  advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases recoveryAdvance_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next item output result
            rw [nextEq] at tail
            exact .next
              (no_topItemRecoveryStops_of_nonBoundary_token guardFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every executable recovery success consumes its mandatory first token and
then follows the exact boundary-preserving scan. -/
theorem recoverTopItem_success_ordinaryOutcome_sound
    {input output : State} {item : TopItem}
    (result : recoverTopItem input = .ok item output) :
    DeclarativeGrammar.TopItemRecoveryParses
      input.declarativeRemainder item output.declarativeRemainder := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoveryAdvance_state_shape advanced with ⟨found, nextEq⟩
      have scan := recoverTopItemAux_success_ordinaryOutcome_sound token.span
        (next.remainingCount + 1) token.span next item output result
      rw [nextEq] at scan
      exact .recovered (tokenAt_of_peek?_eq_some found) scan

/-- Every executable recovery rejection exactly records an unavailable
mandatory first token and retains the complete declarative remainder. -/
theorem recoverTopItem_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : recoverTopItem input = .reject failure rejected) :
    DeclarativeGrammar.TopItemRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverTopItem at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      by_cases atEnd : input.window.endIndex ≤ input.cursor
      · exact .windowEnd atEnd
      · have inside : input.cursor < input.window.endIndex := by omega
        apply DeclarativeGrammar.TopItemRecoveryRejects.missingToken inside
        unfold State.advance? State.peek? at advanced
        simpa [State.declarativeRemainder, inside] using advanced
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverTopItemAux_production_exists_ok token.span token.span next
          with ⟨recovered, output, recoveredResult⟩
      rw [recoveredResult] at result
      contradiction

/-- Package standalone top-item recovery success and rejection. -/
theorem recoverTopItem_ordinaryOutcome_sound :
    (∀ {input output : State} {item : TopItem},
      recoverTopItem input = .ok item output →
        DeclarativeGrammar.TopItemRecoveryParses
          input.declarativeRemainder item output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverTopItem input = .reject failure rejected →
        DeclarativeGrammar.TopItemRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverTopItem_success_ordinaryOutcome_sound,
    recoverTopItem_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic standalone recovery outcomes. -/
theorem recoverTopItem_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TopItemRecoveryParses
      DeclarativeGrammar.TopItemRecoveryRejects :=
  DeclarativeGrammar.topItemRecoveryDeterministicOutcomeSpec

/-- Standalone recovery fixes the full error-item AST and both outcome endpoints. -/
theorem recoverTopItem_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TopItemRecoveryParses DeclarativeGrammar.TopItemRecoveryRejects :=
  DeclarativeGrammar.topItemRecoveryExactOutcomeSpec

/-- Recovery successes agree on their complete AST and declarative remainder. -/
theorem recoverTopItem_success_result_unique
    {input leftOutput rightOutput : State} {left right : TopItem}
    (leftResult : recoverTopItem input = .ok left leftOutput)
    (rightResult : recoverTopItem input = .ok right rightOutput) :
    left = right ∧ leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  recoverTopItem_exactOutcomeSpec.successResultUnique
    (recoverTopItem_success_ordinaryOutcome_sound leftResult)
    (recoverTopItem_success_ordinaryOutcome_sound rightResult)

/-- Recovery rejections agree on their original-input declarative endpoint. -/
theorem recoverTopItem_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : recoverTopItem input = .reject leftFailure leftOutput)
    (rightResult : recoverTopItem input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  recoverTopItem_exactOutcomeSpec.rejectOutputUnique
    (recoverTopItem_reject_ordinaryOutcome_sound leftResult)
    (recoverTopItem_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser.FileInternals
