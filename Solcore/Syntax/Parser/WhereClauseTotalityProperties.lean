import Solcore.Syntax.Parser.PredicateSequenceTotalityProperties
import Solcore.Syntax.Parser.WhereClauseProperties

/-! Valid-input totality for canonical optional `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional `where` parsing is ordinary in both present and absent paths. -/
theorem whereClause_invariantFreeOnValid :
    Parser.InvariantFreeOnValid whereClause := by
  unfold whereClause
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isContextual observed .where
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (contextual_validFor .where .typeExpr)
      (contextual_ordinary .where .typeExpr).invariantFreeOnValid
    intro marker
    apply Parser.bind_invariantFreeOnValid
      PredicateInternals.predicateSequence_validFor
      PredicateInternals.predicateSequence_invariantFreeOnValid
    intro predicates
    exact Parser.pure_invariantFreeOnValid (some ({
      span := SourceSpan.cover marker.span predicates.span
      predicates := predicates.elements
    } : WhereClause))
  · simp only [present, Bool.false_eq_true, if_false]
    exact Parser.pure_invariantFreeOnValid none

theorem whereClause_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ clause next, whereClause input = .ok clause next) ∨
      (∃ failure next, whereClause input = .reject failure next) :=
  whereClause_invariantFreeOnValid input inputValid

theorem whereClause_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    whereClause input ≠ .invariant error :=
  whereClause_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
