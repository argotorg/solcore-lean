import Solcore.Syntax.Parser.FunctionModifierSoundnessProperties
import Solcore.Syntax.Parser.FunctionParametersSoundnessProperties
import Solcore.Syntax.Parser.GenericParametersSoundnessProperties
import Solcore.Syntax.Parser.PredicateSequenceDiagnosticReflectionProperties
import Solcore.Syntax.Parser.ReturnClauseSoundnessProperties
import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.WhereClauseSoundnessProperties

/-! Diagnostic-free success soundness for complete function signatures. -/

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

/-- Every diagnostic-free complete signature follows its location policy and
strict parser-independent grammar. -/
theorem functionSignature_success_sound (location : FunctionLocation)
    {input next : State} {signature : FunctionSignature}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature location input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
      (match location with
      | .module => DeclarativeGrammar.ModuleFunctionModifiersAllowed
      | .contract => DeclarativeGrammar.ContractFunctionModifiersAllowed)
      input.declarativeRemainder signature next.declarativeRemainder := by
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
  have afterReturnsFree := whereClause_reflectsDiagnosticFreeOnSuccess
    afterReturns whereClause next whereResult diagnosticFree
  have afterModifiersFree := returnClause_reflectsDiagnosticFreeOnSuccess
    afterModifiers returnsClause afterReturns returnsResult afterReturnsFree
  have afterParametersFree :=
    functionModifiers_reflectsDiagnosticFreeOnSuccess location afterParameters
      modifiers afterModifiers modifiersResult afterModifiersFree
  have keywordGrammar := keyword_success_exactTokenParses .functionKw
    .topItem keywordResult
  have nameGrammar := identifier_success_sound .topItem nameResult
  have genericsGrammar := optionalGenericParameters_success_sound
    genericsResult
  have parametersGrammar := functionParameters_success_sound
    afterParametersFree parametersResult
  have modifiersGrammar := functionModifiers_success_sound location
    modifiersResult
  have returnsGrammar := returnClause_success_sound returnsResult
  have whereGrammar := whereClause_success_sound whereResult
  cases location with
  | module =>
      have policy := functionModifiers_module_success_allowed
        afterModifiersFree modifiersResult
      simpa only [signatureEnd_eq] using
        (DeclarativeGrammar.FunctionSignatureParses.parsed functionToken.span
          keywordGrammar nameGrammar genericsGrammar parametersGrammar
          modifiersGrammar returnsGrammar whereGrammar policy)
  | contract =>
      have policy := functionModifiers_contract_success_allowed modifiersResult
      simpa only [signatureEnd_eq] using
        (DeclarativeGrammar.FunctionSignatureParses.parsed functionToken.span
          keywordGrammar nameGrammar genericsGrammar parametersGrammar
          modifiersGrammar returnsGrammar whereGrammar policy)

/-- Signature grammar soundness composes with retained-source validity. -/
theorem functionSignature_success_sound_and_validFor
    (location : FunctionLocation) {input next : State}
    {signature : FunctionSignature} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature location input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
        (match location with
        | .module => DeclarativeGrammar.ModuleFunctionModifiersAllowed
        | .contract => DeclarativeGrammar.ContractFunctionModifiersAllowed)
        input.declarativeRemainder signature next.declarativeRemainder ∧
      FunctionSignature.ValidFor input.file signature := by
  refine ⟨functionSignature_success_sound location diagnosticFree result, ?_⟩
  have valid := functionSignature_validFor location input inputValid
  rw [result] at valid
  exact valid.1

/-- Module signature success specializes the generic location policy. -/
theorem functionSignature_module_success_sound {input next : State}
    {signature : FunctionSignature} (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .module input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
      DeclarativeGrammar.ModuleFunctionModifiersAllowed
      input.declarativeRemainder signature next.declarativeRemainder :=
  functionSignature_success_sound .module diagnosticFree result

/-- Contract signature success specializes the generic location policy. -/
theorem functionSignature_contract_success_sound {input next : State}
    {signature : FunctionSignature} (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .contract input = .ok signature next) :
    DeclarativeGrammar.FunctionSignatureParses
      DeclarativeGrammar.ContractFunctionModifiersAllowed
      input.declarativeRemainder signature next.declarativeRemainder :=
  functionSignature_success_sound .contract diagnosticFree result

end Solcore.Syntax.Parser
