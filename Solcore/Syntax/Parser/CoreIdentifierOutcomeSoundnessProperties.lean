import Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-!
Exact executable ordinary outcomes for the checked Core identifier primitive.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rawIdentifier_reject_state_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
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

/-- Checked-identifier rejection never consumes or otherwise changes state. -/
theorem identifier_reject_state_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected = input := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | invariant error => simp [raw] at result
  | ok name afterName =>
      simp only [raw] at result
      split at result <;> contradiction
  | reject rejectedFailure rejectedState =>
      simp only [raw] at result
      cases result
      exact rawIdentifier_reject_state_eq context raw

/-- Checked-identifier rejection proves carrier-level identifier absence. -/
theorem identifier_reject_identifierAbsentAt (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
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
  unfold identifier at result
  simp only [rawIdentifier, found] at result
  split at result <;> contradiction

/-- Every executable checked-identifier rejection follows the exact
non-consuming parser-independent rejection relation. -/
theorem identifier_reject_sound (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    DeclarativeGrammar.IdentifierRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  have rejectedEq := identifier_reject_state_eq context result
  subst rejectedEq
  exact .absent (identifier_reject_identifierAbsentAt context result)

end Solcore.Syntax.Parser
