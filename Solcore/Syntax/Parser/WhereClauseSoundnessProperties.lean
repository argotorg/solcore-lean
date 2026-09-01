import Solcore.Syntax.Parser.PredicateSequenceSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseProperties

/-! Success soundness for optional canonical `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful optional `where` follows its marker-prioritized grammar. -/
theorem whereClause_success_sound {input next : State}
    {clause : Option WhereClause}
    (result : whereClause input = .ok clause next) :
    DeclarativeGrammar.OptionalWhereClauseParses
      input.declarativeRemainder clause next.declarativeRemainder := by
  unfold whereClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .where
  · simp only [present, if_true] at result
    rcases predicateBind_ok_components result with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases predicateBind_ok_components rest with
      ⟨predicates, afterPredicates, predicatesResult, finished⟩
    cases finished
    exact .present marker.span
      (contextual_success_exactTokenParses .where .typeExpr markerResult)
      (PredicateInternals.predicateSequence_success_sound predicatesResult)
  · have absent : isContextual input .where = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (contextualAbsentAt_of_isContextual_eq_false .where absent)

/-- Optional-where grammar soundness composes with source validity. -/
theorem whereClause_success_sound_and_validFor {input next : State}
    {clause : Option WhereClause} (inputValid : input.ValidFor)
    (result : whereClause input = .ok clause next) :
    DeclarativeGrammar.OptionalWhereClauseParses
        input.declarativeRemainder clause next.declarativeRemainder ∧
      Option.ValidFor WhereClause.ValidFor input.file clause := by
  refine ⟨whereClause_success_sound result, ?_⟩
  have valid := whereClause_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
