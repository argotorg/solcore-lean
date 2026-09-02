import Solcore.Syntax.Parser.BarePredicateSequenceOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.PredicateSequenceSoundnessProperties

/-! Exact executable rejection reflection for grouped-first predicate choice. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem openingPresent_of_isSymbol_eq_true {input : State}
    (present : isSymbol input .leftParen = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .leftParen } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr present with
    ⟨opening, parsed⟩
  exact ⟨opening.span,
    (symbol_success_exactTokenParses .leftParen .typeExpr parsed).1⟩

/-- Every rejected predicate sequence retains exact grouped-first dispatch and
the final bare rejection remainder. -/
theorem predicateSequence_reject_sound
    {input rejected : State} {failure : Failure}
    (result : predicateSequence input = .reject failure rejected) :
    DeclarativeGrammar.PredicateSequenceRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold predicateSequence at result
  split at result
  · rename_i openingPresent
    unfold orElse at result
    cases groupedResult : groupedPredicates input with
    | ok grouped afterGrouped => simp [groupedResult] at result
    | invariant error => simp [groupedResult] at result
    | reject groupedFailure groupedRejected =>
        simp only [groupedResult] at result
        exact .fallback
          (openingPresent_of_isSymbol_eq_true openingPresent)
          (groupedPredicates_reject_sound groupedResult)
          (barePredicates_reject_sound result)
  · rename_i openingAbsent
    exact .direct
      (symbolAbsentAt_of_isSymbol_eq_false .leftParen
        (Bool.eq_false_iff.mpr openingAbsent))
      (barePredicates_reject_sound result)

/-- Package executable predicate-sequence success and exact rejection. -/
theorem predicateSequence_ordinaryOutcome_sound :
    (∀ {input next : State} {values : PredicateSequence},
      predicateSequence input = .ok values next →
        DeclarativeGrammar.PredicateSequenceParses
          input.declarativeRemainder values next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      predicateSequence input = .reject failure rejected →
        DeclarativeGrammar.PredicateSequenceRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨predicateSequence_success_sound, predicateSequence_reject_sound⟩

end Solcore.Syntax.Parser.PredicateInternals
