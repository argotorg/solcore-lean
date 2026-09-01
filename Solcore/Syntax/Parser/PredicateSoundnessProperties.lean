import Solcore.Syntax.Parser.PredicateProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Success soundness for one trait predicate. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful predicate follows its exact recursive type grammar. -/
theorem predicate_success_sound {input next : State} {value : Predicate}
    (result : predicate input = .ok value next) :
    DeclarativeGrammar.PredicateParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold predicate at result
  rcases predicateBind_ok_components result with
    ⟨subject, afterSubject, subjectResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨colon, afterColon, colonResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  have argumentsGrammar := parseNamedTypeArguments_success_sound typeExpr
    typeExpr_success_sound typeExpr_preservesTokenWindow argumentsResult
  cases arguments <;>
    exact .parsed colon.span
      (typeExpr_success_sound subjectResult)
      (symbol_success_exactTokenParses .colon .typeExpr colonResult)
      (identifier_success_sound .typeExpr nameResult) argumentsGrammar

/-- Predicate grammar soundness composes with source validity. -/
theorem predicate_success_sound_and_validFor {input next : State}
    {value : Predicate} (inputValid : input.ValidFor)
    (result : predicate input = .ok value next) :
    DeclarativeGrammar.PredicateParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      Predicate.ValidFor input.file value := by
  refine ⟨predicate_success_sound result, ?_⟩
  have valid := predicate_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
