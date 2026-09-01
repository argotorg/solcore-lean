import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.PredicateSequenceProperties
import Solcore.Syntax.Parser.PredicateSoundnessProperties

/-! Success soundness for parenthesized predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

/-- Every successful grouped sequence follows the generic delimiter grammar. -/
theorem groupedPredicates_success_sound {input next : State}
    {values : PredicateSequence}
    (result : groupedPredicates input = .ok values next) :
    DeclarativeGrammar.GroupedPredicateSequenceParses
      input.declarativeRemainder values next.declarativeRemainder := by
  unfold groupedPredicates at result
  rcases predicateBind_ok_components result with
    ⟨parsed, afterParsed, parsedResult, finished⟩
  have grammar := delimited_nonempty_trailing_success_sound .leftParen
    .rightParen predicate DeclarativeGrammar.PredicateParses .typeExpr
    .topLevel predicate_success_sound predicate_preservesTokenWindow
    parsedResult
  cases elements : parsed.elements with
  | nil =>
      simp [elements] at finished
  | cons head tail =>
      simp only [elements, pure] at finished
      have parsedEq : parsed = {
          span := parsed.span
          elements := head :: tail
        } := by
        rcases parsed with ⟨span, parsedElements⟩
        simp only at elements ⊢
        rw [elements]
      rw [parsedEq] at grammar
      cases finished
      simpa [DeclarativeGrammar.GroupedPredicateSequenceParses,
        NonemptyList.toList] using grammar

/-- Grouped sequence grammar soundness composes with source validity. -/
theorem groupedPredicates_success_sound_and_validFor {input next : State}
    {values : PredicateSequence} (inputValid : input.ValidFor)
    (result : groupedPredicates input = .ok values next) :
    DeclarativeGrammar.GroupedPredicateSequenceParses
        input.declarativeRemainder values next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file values := by
  refine ⟨groupedPredicates_success_sound result, ?_⟩
  have valid := groupedPredicates_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.PredicateInternals
