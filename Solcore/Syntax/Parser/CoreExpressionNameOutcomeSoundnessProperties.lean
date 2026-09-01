import Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreLiteralSoundnessProperties

/-! Exact executable ordinary outcomes for one Boolean-first Core name. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem booleanIdentifier_ne_reject_of_isBooleanValue
    {input rejected : State} {failure : Failure}
    (starts : isBooleanValue input = true)
    (result : booleanIdentifier input = .reject failure rejected) : False := by
  unfold isBooleanValue isKeyword State.peekKind? at starts
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none => simp [found] at starts
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at starts result
      all_goals try { contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at starts result
        all_goals try { contradiction }

/-- Every executable expression-name rejection is the exact identifier-token
absence branch after both Boolean guards fail. -/
theorem expressionName_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : expressionName input = .reject failure rejected) :
    DeclarativeGrammar.ExpressionNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold expressionName at result
  by_cases starts : isBooleanValue input = true
  · simp only [starts, if_true] at result
    exact False.elim
      (booleanIdentifier_ne_reject_of_isBooleanValue starts result)
  · have startsFalse : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr starts
    simp only [startsFalse, Bool.false_eq_true, if_false] at result
    have rejectedEq := identifier_reject_state_eq .expression result
    subst rejected
    have booleanAbsences :
        isKeyword input .trueKw = false ∧
          isKeyword input .falseKw = false :=
      Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using startsFalse)
    exact .absent ⟨
      keywordAbsentAt_of_isKeyword_eq_false .trueKw booleanAbsences.1,
      keywordAbsentAt_of_isKeyword_eq_false .falseKw booleanAbsences.2,
      identifier_reject_identifierAbsentAt .expression result⟩

/-- Package the existing unconditional success bridge with exact rejection. -/
theorem expressionName_ordinaryOutcome_sound :
    (∀ {input output : State} {name : Identifier},
      expressionName input = .ok name output →
        DeclarativeGrammar.ExpressionNameOrdinaryParses
          input.declarativeRemainder name output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionName input = .reject failure rejected →
        DeclarativeGrammar.ExpressionNameRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨expressionName_success_sound, expressionName_reject_ordinary_sound⟩

/-- Re-export the deterministic expression-name outcome at its executable
boundary. -/
theorem expressionName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExpressionNameOrdinaryParses
      DeclarativeGrammar.ExpressionNameRejects :=
  DeclarativeGrammar.expressionNameDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ExpressionAtomInternals
