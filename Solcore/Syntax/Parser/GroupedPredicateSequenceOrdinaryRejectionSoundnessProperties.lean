import Solcore.Syntax.DeclarativePredicateOutcomeProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.GroupedPredicateSequenceSoundnessProperties
import Solcore.Syntax.Parser.PredicateOrdinaryRejectionSoundnessProperties

/-! Exact executable ordinary rejection for grouped predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

/-- Every grouped-predicate rejection is the exact rejection of its required
nonempty, allow-trailing parenthesized predicate list. -/
theorem groupedPredicates_reject_sound
    {input rejected : State} {failure : Failure}
    (result : groupedPredicates input = .reject failure rejected) :
    DeclarativeGrammar.GroupedPredicateSequenceRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold groupedPredicates at result
  cases parsedResult : delimited .leftParen .rightParen false predicate
      .typeExpr .topLevel input with
  | invariant error => simp [bind, parsedResult] at result
  | reject parsedFailure parsedRejected =>
      simp only [bind, parsedResult] at result
      cases result
      exact delimited_reject_sound .leftParen .rightParen false predicate
        DeclarativeGrammar.PredicateParses
        DeclarativeGrammar.PredicateRejects .typeExpr .topLevel
        predicate_success_sound predicate_reject_sound parsedResult
  | ok parsed afterParsed =>
      simp only [bind, parsedResult] at result
      cases elements : parsed.elements <;> simp [elements, pure] at result

/-- Package executable grouped-predicate success and exact ordinary
rejection. -/
theorem groupedPredicates_ordinaryOutcome_sound :
    (∀ {input next : State} {values : PredicateSequence},
      groupedPredicates input = .ok values next →
        DeclarativeGrammar.GroupedPredicateSequenceParses
          input.declarativeRemainder values next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      groupedPredicates input = .reject failure rejected →
        DeclarativeGrammar.GroupedPredicateSequenceRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨groupedPredicates_success_sound, groupedPredicates_reject_sound⟩

end Solcore.Syntax.Parser.PredicateInternals
