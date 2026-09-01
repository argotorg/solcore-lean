import Solcore.Syntax.DeclarativeYulStatementTerminatedOutcomeProperties
import Solcore.Syntax.Parser.CoreYulStatementBasicSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Yul.StatementProperties

/-!
Unconditional ordinary-success and exact-rejection reflection for a Yul
statement core followed by its optional semicolon.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem reject_state_eq {α : Type}
    {leftFailure rightFailure : Failure} {leftState rightState : State}
    (result : (Reply.reject leftFailure leftState : Reply α) =
      .reject rightFailure rightState) :
    leftState = rightState := by
  injection result

/-- Optional-semicolon parsing has no rejection outcome. -/
private theorem optionalYulSemicolon_not_reject (value : YulStmt)
    {input rejected : State} {failure : Failure}
    (result : optionalYulSemicolon value input =
      .reject failure rejected) : False := by
  unfold optionalYulSemicolon getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .semicolon = true
  · simp only [present, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .yulStatement present
      with ⟨semicolon, semicolonResult⟩
    simp only [semicolonResult, pure] at result
    contradiction
  · simp only [present, Bool.false_eq_true, if_false, pure] at result
    contradiction

/-- Every successful executable optional termination reflects an ordinary
terminated success whenever its core success does. -/
theorem yulStatementTerminated_success_ordinary_sound
    (nested : Parser YulStmt)
    (coreOrdinary : DeclarativeGrammar.Remainder → YulStmt →
      DeclarativeGrammar.Remainder → Prop)
    (coreSuccessSound : ∀ {input output : State} {statement : YulStmt},
      yulStatementCore nested input = .ok statement output →
        coreOrdinary input.declarativeRemainder statement
          output.declarativeRemainder)
    {input output : State} {statement : YulStmt}
    (result : yulStatementTerminated nested input = .ok statement output) :
    DeclarativeGrammar.YulStatementTerminatedOrdinaryParses coreOrdinary
      input.declarativeRemainder statement output.declarativeRemainder := by
  unfold yulStatementTerminated at result
  cases coreResult : yulStatementCore nested input with
  | invariant error => simp [bind, coreResult] at result
  | reject failure rejected => simp [bind, coreResult] at result
  | ok coreValue afterCore =>
      simp only [bind, coreResult] at result
      have valueEq := optionalYulSemicolon_value_eq coreValue statement
        afterCore output result
      subst statement
      exact ⟨afterCore.declarativeRemainder,
        coreSuccessSound coreResult,
        optionalYulSemicolon_success_sound coreValue result⟩

/-- Every executable rejection of optional termination is exactly the core
rejection, since optional-semicolon parsing itself cannot reject. -/
theorem yulStatementTerminated_reject_ordinary_sound
    (nested : Parser YulStmt)
    (coreRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (coreRejectSound : ∀ {input rejected : State} {failure : Failure},
      yulStatementCore nested input = .reject failure rejected →
        coreRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : yulStatementTerminated nested input =
      .reject failure rejected) :
    DeclarativeGrammar.YulStatementTerminatedRejects coreRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold yulStatementTerminated at result
  cases coreResult : yulStatementCore nested input with
  | invariant error => simp [bind, coreResult] at result
  | reject coreFailure afterCore =>
      simp only [bind, coreResult] at result
      have stateEq := reject_state_eq result
      cases stateEq
      exact coreRejectSound coreResult
  | ok coreValue afterCore =>
      simp only [bind, coreResult] at result
      exact False.elim (optionalYulSemicolon_not_reject coreValue result)

end Solcore.Syntax.Parser
