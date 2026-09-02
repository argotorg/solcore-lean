import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeGrammar
import Solcore.Syntax.Parser.FunctionModifierSoundnessProperties
import Solcore.Syntax.Parser.FunctionParametersOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.ReturnClauseOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties

/-! Ordinary success soundness for complete named-function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem signatureEnd_eq
    (parameters : DelimitedList FunctionParameter)
    (modifiers : FunctionModifiers) (returnsClause : Option ReturnClause)
    (whereClause : Option WhereClause) :
    SignatureInternals.signatureEnd parameters modifiers returnsClause
        whereClause =
      DeclarativeGrammar.functionSignatureEnd parameters modifiers
        returnsClause whereClause := by
  rfl

/-- Every successful complete signature follows the recovery-aware ordinary
grammar, independently of its executable location policy. -/
theorem functionSignature_success_ordinaryOutcome_sound
    (location : FunctionLocation) {input output : State}
    {signature : FunctionSignature}
    (result : functionSignature location input = .ok signature output) :
    DeclarativeGrammar.FunctionSignatureOrdinaryParses
      input.declarativeRemainder signature output.declarativeRemainder := by
  unfold functionSignature at result
  rcases bind_ok_components result with
    ⟨functionToken, afterKeyword, keywordResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases bind_ok_components rest with
    ⟨genericParameters, afterGenerics, genericsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨modifiers, afterModifiers, modifiersResult, rest⟩
  rcases bind_ok_components rest with
    ⟨returnsClause, afterReturns, returnsResult, rest⟩
  rcases bind_ok_components rest with
    ⟨whereClause, afterWhere, whereResult, finished⟩
  cases finished
  have keywordGrammar := keyword_success_exactTokenParses .functionKw
    .topItem keywordResult
  have nameGrammar := identifier_success_sound .topItem nameResult
  have genericsGrammar := optionalGenericParameters_ordinaryOutcome_sound.1
    genericsResult
  have parametersGrammar := functionParameters_success_ordinaryOutcome_sound
    parametersResult
  have modifiersGrammar := functionModifiers_success_sound location
    modifiersResult
  have returnsGrammar := returnClause_ordinaryOutcome_sound.1 returnsResult
  have whereGrammar := whereClause_ordinaryOutcome_sound.1 whereResult
  simpa only [signatureEnd_eq] using
    (DeclarativeGrammar.FunctionSignatureOrdinaryParses.parsed
      functionToken.span keywordGrammar nameGrammar genericsGrammar
      parametersGrammar modifiersGrammar returnsGrammar whereGrammar)

end Solcore.Syntax.Parser
