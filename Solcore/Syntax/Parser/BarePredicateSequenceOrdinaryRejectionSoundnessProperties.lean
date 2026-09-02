import Solcore.Syntax.DeclarativePredicateSequenceOutcomeProperties
import Solcore.Syntax.Parser.BarePredicateSequenceSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.PredicateOrdinaryRejectionSoundnessProperties

/-! Exact executable rejection reflection for bare predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem barePredicatesTail_reject_sound
    (first : Predicate) : ∀ fuel last tailRev input failure rejected,
      barePredicatesTail first fuel last tailRev input =
          .reject failure rejected →
        DeclarativeGrammar.BarePredicateTailRejects
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [barePredicatesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold barePredicatesTail at result
      split at result
      · rename_i commaPresent
        cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at result
        | reject commaFailure commaRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .comma .typeExpr
              commaPresent with ⟨comma, parsed⟩
            rw [parsed] at commaResult
            contradiction
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaParsed := symbol_success_exactTokenParses .comma
              .typeExpr commaResult
            split at result
            · rename_i typePresent
              have nextStarts :=
                typeExprStartsAt_of_startsTypeExpr_eq_true typePresent
              cases predicateResult : predicate afterComma with
              | invariant error => simp [predicateResult] at result
              | reject predicateFailure predicateRejected =>
                  simp only [predicateResult] at result
                  cases result
                  exact .predicateRejected comma.span commaParsed nextStarts
                    (predicate_reject_sound predicateResult)
              | ok value afterPredicate =>
                  simp only [predicateResult] at result
                  exact .next comma.span commaParsed nextStarts
                    (predicate_success_sound predicateResult)
                    (inductionHypothesis value (value :: tailRev)
                      afterPredicate failure rejected result)
            · simp at result
      · simp at result

/-- Every rejected bare sequence records its exact first rejected stage. -/
theorem barePredicates_reject_sound
    {input rejected : State} {failure : Failure}
    (result : barePredicates input = .reject failure rejected) :
    DeclarativeGrammar.BarePredicateSequenceRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold barePredicates at result
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (predicate_reject_sound firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (predicate_success_sound firstResult)
        (barePredicatesTail_reject_sound first
          (afterFirst.remainingCount + 1) first [] afterFirst failure
            rejected result)

/-- Package executable bare-sequence success and exact rejection. -/
theorem barePredicates_ordinaryOutcome_sound :
    (∀ {input next : State} {values : PredicateSequence},
      barePredicates input = .ok values next →
        DeclarativeGrammar.BarePredicateSequenceParses
          input.declarativeRemainder values next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      barePredicates input = .reject failure rejected →
        DeclarativeGrammar.BarePredicateSequenceRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨barePredicates_success_sound, barePredicates_reject_sound⟩

end Solcore.Syntax.Parser.PredicateInternals
