import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Exact executable ordinary outcomes for the raw identifier primitive. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rawIdentifier_reject_state_eq_forOutcome
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    rejected = input := by
  unfold rawIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      cases result
      rfl
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; cases result; rfl }
      case identifier text => contradiction

private theorem rawIdentifier_reject_identifierAbsentAt
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
  rintro ⟨span, text, inside, atCursor⟩
  have found : input.peek? = some {
      span
      value := TokenKind.identifier text
    } := by
    unfold State.peek?
    change input.cursor < input.window.endIndex at inside
    change input.tokens[input.cursor]? = some {
      span
      value := TokenKind.identifier text
    } at atCursor
    simp only [inside, ↓reduceIte, atCursor]
  unfold rawIdentifier at result
  simp only [found] at result
  contradiction

/-- Raw-identifier success is one exact identifier transition. -/
theorem rawIdentifier_success_ordinaryOutcome_sound
    (context : ParseContext) {input output : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name output) :
    DeclarativeGrammar.IdentifierParses input.declarativeRemainder name
      output.declarativeRemainder := by
  rcases rawIdentifier_ok_tokenAt context result with ⟨token, outputEq⟩
  subst output
  exact ⟨token, rfl, rfl, rfl⟩

/-- Raw-identifier rejection is exact and nonconsuming. -/
theorem rawIdentifier_reject_ordinaryOutcome_sound
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : rawIdentifier context input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := rawIdentifier_reject_state_eq_forOutcome context result
  subst rejected
  exact .absent (rawIdentifier_reject_identifierAbsentAt context result)

/-- Package raw-identifier success and exact rejection. -/
theorem rawIdentifier_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {name : Identifier},
      rawIdentifier context input = .ok name output →
        DeclarativeGrammar.IdentifierParses input.declarativeRemainder name
          output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      rawIdentifier context input = .reject failure rejected →
        DeclarativeGrammar.IdentifierRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨rawIdentifier_success_ordinaryOutcome_sound context,
    rawIdentifier_reject_ordinaryOutcome_sound context⟩

/-- Raw identifiers reuse the deterministic identifier outcome contract. -/
theorem rawIdentifier_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.IdentifierParses
      DeclarativeGrammar.IdentifierRejects :=
  DeclarativeGrammar.identifierDeterministicOutcomeSpec

end Solcore.Syntax.Parser
