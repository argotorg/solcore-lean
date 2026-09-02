import Solcore.Syntax.DeclarativeImplDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ImplBodyOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.ImplDefaultMarkerOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ImplHeadArgumentsOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties

/-! Broad ordinary-success soundness for complete implementation declarations. -/

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

/-- Every executable implementation success records its exact optional
default marker, head stages, broad body, AST span, and final remainder without
a diagnostic-free premise. -/
theorem implDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ImplDecl}
    (result : implDecl input = .ok declaration output) :
    DeclarativeGrammar.ImplDeclOrdinaryParses input.declarativeRemainder
      declaration output.declarativeRemainder := by
  unfold implDecl at result
  rcases bind_ok_components result with
    ⟨defaultMarker, afterDefault, defaultResult, suffix⟩
  unfold ImplInternals.implDeclAfterDefault at suffix
  rcases bind_ok_components suffix with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨values, afterValues, valuesResult, rest⟩
  rcases bind_ok_components rest with
    ⟨headArguments, afterArguments, argumentsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact .parsed
    (ImplInternals.implDefaultMarker_success_ordinaryOutcome_sound
      defaultResult)
    marker.span
    (contextual_success_exactTokenParses .impl .topItem markerResult)
    (optionalGenericParameters_ordinaryOutcome_sound.1 genericsResult)
    (identifier_success_sound .topItem nameResult)
    (ImplInternals.implHeadArguments_success_ordinaryOutcome_sound
      valuesResult argumentsResult)
    (whereClause_ordinaryOutcome_sound.1 whereResult)
    (ImplInternals.implBody_success_ordinaryOutcome_sound bodyResult)

end Solcore.Syntax.Parser
