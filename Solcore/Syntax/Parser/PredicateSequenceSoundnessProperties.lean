import Solcore.Syntax.Parser.BarePredicateSequenceSoundnessProperties
import Solcore.Syntax.Parser.GroupedPredicateSequenceOrdinaryRejectionSoundnessProperties

/-! Success soundness for predicate-sequence branch selection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem groupedUnavailable_of_opening_absent {input : State}
    (openingAbsent : isSymbol input .leftParen = false) :
    DeclarativeGrammar.GroupedPredicateSequenceUnavailable
      input.declarativeRemainder := by
  rintro ⟨values, output, grouped⟩
  unfold DeclarativeGrammar.GroupedPredicateSequenceParses at grouped
  rcases grouped with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact symbolAbsentAt_of_isSymbol_eq_false .leftParen openingAbsent
    ⟨openingSpan, openingToken⟩

/-- Every successful sequence records exact grouped-first branch priority. -/
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
        exact .bare
          (groupedPredicates_reject_sound groupedResult).no_parse
          (barePredicates_success_sound result)
    | invariant error =>
        simp [groupedResult] at result
  · rename_i openingAbsent
    exact .bare
      (groupedUnavailable_of_opening_absent
        (Bool.eq_false_iff.mpr openingAbsent))
      (barePredicates_success_sound result)

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
