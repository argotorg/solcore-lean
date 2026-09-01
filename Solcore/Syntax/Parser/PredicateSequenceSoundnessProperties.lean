import Solcore.Syntax.Parser.BarePredicateSequenceSoundnessProperties
import Solcore.Syntax.Parser.GroupedPredicateSequenceSoundnessProperties

/-! Success soundness for predicate-sequence branch selection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

/-- Every successful sequence belongs to its grouped-or-bare grammar union. -/
theorem predicateSequence_success_sound {input next : State}
    {values : PredicateSequence}
    (result : predicateSequence input = .ok values next) :
    DeclarativeGrammar.PredicateSequenceParses
      input.declarativeRemainder values next.declarativeRemainder := by
  unfold predicateSequence at result
  split at result
  · unfold orElse at result
    cases groupedResult : groupedPredicates input with
    | ok grouped afterGrouped =>
        simp only [groupedResult] at result
        cases result
        exact .grouped (groupedPredicates_success_sound groupedResult)
    | reject failure rejected =>
        simp only [groupedResult] at result
        exact .bare (barePredicates_success_sound result)
    | invariant error =>
        simp [groupedResult] at result
  · exact .bare (barePredicates_success_sound result)

/-- Sequence-union soundness composes with source validity. -/
theorem predicateSequence_success_sound_and_validFor {input next : State}
    {values : PredicateSequence} (inputValid : input.ValidFor)
    (result : predicateSequence input = .ok values next) :
    DeclarativeGrammar.PredicateSequenceParses
        input.declarativeRemainder values next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file values := by
  refine ⟨predicateSequence_success_sound result, ?_⟩
  have valid := predicateSequence_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.PredicateInternals
