import Solcore.Syntax.DeclarativeTraitDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.TraitBodyOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties

/-! Broad ordinary-success soundness for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable trait declaration records its exact marker, name,
required generic parameters, optional where clause, broad body, AST, and
remainder without a diagnostic-free premise. -/
theorem traitDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : TraitDecl}
    (result : traitDecl input = .ok declaration output) :
    DeclarativeGrammar.TraitDeclOrdinaryParses input.declarativeRemainder
      declaration output.declarativeRemainder := by
  unfold traitDecl at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed marker.span
    (contextual_success_exactTokenParses .trait .topItem markerResult)
    (identifier_success_sound .topItem nameResult)
    (genericParameters_ordinaryOutcome_sound.1 genericsResult)
    (whereClause_ordinaryOutcome_sound.1 whereResult)
    (TraitInternals.traitBody_success_ordinaryOutcome_sound bodyResult)

end Solcore.Syntax.Parser
