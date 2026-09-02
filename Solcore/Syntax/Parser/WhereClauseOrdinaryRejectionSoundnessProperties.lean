import Solcore.Syntax.DeclarativeWhereClauseOutcomeProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.PredicateSequenceOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseSoundnessProperties

/-! Exact executable rejection reflection for optional canonical `where`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable optional-`where` rejection is the committed predicate
sequence rejection after its positively guarded marker. -/
theorem whereClause_reject_sound
    {input rejected : State} {failure : Failure}
    (result : whereClause input = .reject failure rejected) :
    DeclarativeGrammar.OptionalWhereClauseRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold whereClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .where
  · rcases contextual_eq_ok_of_isContextual_eq_true .where .typeExpr
        present with ⟨marker, markerResult⟩
    simp only [present, if_true, markerResult] at result
    cases predicatesResult : PredicateInternals.predicateSequence
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [predicatesResult] at result
    | ok predicates afterPredicates =>
        simp [predicatesResult, pure] at result
    | reject predicatesFailure predicatesRejected =>
        simp only [predicatesResult] at result
        cases result
        exact .predicatesRejected marker.span
          (contextual_success_exactTokenParses .where .typeExpr markerResult)
          (PredicateInternals.predicateSequence_reject_sound predicatesResult)
  · have absent : isContextual input .where = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package executable optional-`where` success and exact rejection. -/
theorem whereClause_ordinaryOutcome_sound :
    (∀ {input next : State} {clause : Option WhereClause},
      whereClause input = .ok clause next →
        DeclarativeGrammar.OptionalWhereClauseParses
          input.declarativeRemainder clause next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      whereClause input = .reject failure rejected →
        DeclarativeGrammar.OptionalWhereClauseRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨whereClause_success_sound, whereClause_reject_sound⟩

end Solcore.Syntax.Parser
