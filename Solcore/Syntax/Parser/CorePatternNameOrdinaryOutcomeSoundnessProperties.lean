import Solcore.Syntax.DeclarativeCorePatternNameOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreLiteralSoundnessProperties
import Solcore.Syntax.Parser.Pattern

/-! Exact executable ordinary outcomes for Boolean-first pattern names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PatternInternals

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

/-- Every pattern-name success follows the diagnostic-inclusive Boolean-first
ordinary relation. -/
theorem patternName_success_ordinary_sound
    {input output : State} {name : Identifier}
    (result : patternName input = .ok name output) :
    DeclarativeGrammar.PatternNameOrdinaryParses input.declarativeRemainder
      name output.declarativeRemainder := by
  unfold patternName at result
  by_cases starts : isBooleanValue input = true
  · simp only [starts, if_true] at result
    exact .boolean (booleanIdentifier_success_sound result)
  · have startsFalse : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr starts
    simp only [startsFalse, Bool.false_eq_true, if_false] at result
    have absences : isKeyword input .trueKw = false ∧
        isKeyword input .falseKw = false :=
      Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using startsFalse)
    exact .identifier
      (keywordAbsentAt_of_isKeyword_eq_false .trueKw absences.1)
      (keywordAbsentAt_of_isKeyword_eq_false .falseKw absences.2)
      (identifier_success_sound .pattern result)

/-- Every pattern-name rejection is the exact non-consuming absence of both
Boolean keywords and an ordinary identifier. -/
theorem patternName_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : patternName input = .reject failure rejected) :
    DeclarativeGrammar.PatternNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold patternName at result
  by_cases starts : isBooleanValue input = true
  · simp only [starts, if_true] at result
    exact False.elim
      (booleanIdentifier_ne_reject_of_isBooleanValue starts result)
  · have startsFalse : isBooleanValue input = false :=
      Bool.eq_false_iff.mpr starts
    simp only [startsFalse, Bool.false_eq_true, if_false] at result
    have rejectedEq := identifier_reject_state_eq .pattern result
    subst rejected
    have absences : isKeyword input .trueKw = false ∧
        isKeyword input .falseKw = false :=
      Bool.or_eq_false_iff.mp (by
        simpa only [isBooleanValue] using startsFalse)
    exact .absent ⟨
      keywordAbsentAt_of_isKeyword_eq_false .trueKw absences.1,
      keywordAbsentAt_of_isKeyword_eq_false .falseKw absences.2,
      identifier_reject_identifierAbsentAt .pattern result⟩

/-- Package both executable pattern-name outcomes. -/
theorem patternName_ordinaryOutcome_sound :
    (∀ {input output : State} {name : Identifier},
      patternName input = .ok name output →
        DeclarativeGrammar.PatternNameOrdinaryParses
          input.declarativeRemainder name output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      patternName input = .reject failure rejected →
        DeclarativeGrammar.PatternNameRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨patternName_success_ordinary_sound, patternName_reject_ordinary_sound⟩

/-- Re-export deterministic pattern-name outcomes. -/
theorem patternName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.PatternNameOrdinaryParses
      DeclarativeGrammar.PatternNameRejects :=
  DeclarativeGrammar.patternNameDeterministicOutcomeSpec

end Solcore.Syntax.Parser.PatternInternals
