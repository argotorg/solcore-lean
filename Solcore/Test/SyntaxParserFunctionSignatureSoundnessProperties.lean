import Solcore.Syntax.Parser.FunctionSignatureSoundnessProperties

/-! External consumers for complete function-signature soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionSignatureSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalFunctionModifierParses
example := @FunctionModifiersParses
example := @ModuleFunctionModifiersAllowed
example := @ContractFunctionModifiersAllowed
example := @functionSignatureEnd
example := @FunctionSignatureParses

example := @optionalFunctionModifier_success_sound
example := @optionalFunctionModifier_success_sound_and_validFor
example := @functionModifiers_success_sound
example := @functionModifiers_success_sound_and_validFor
example := @functionModifiers_module_success_allowed
example := @functionModifiers_contract_success_allowed

example := @genericParameters_reflectsDiagnosticFreeOnSuccess
example := @optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
example := @functionParameters_reflectsDiagnosticFreeOnSuccess
example := @optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess
example := @functionModifiers_reflectsDiagnosticFreeOnSuccess
example := @returnClause_reflectsDiagnosticFreeOnSuccess
example := @predicate_reflectsDiagnosticFreeOnSuccess
example := @PredicateInternals.groupedPredicates_reflectsDiagnosticFreeOnSuccess
example := @PredicateInternals.barePredicates_reflectsDiagnosticFreeOnSuccess
example := @PredicateInternals.predicateSequence_reflectsDiagnosticFreeOnSuccess
example := @whereClause_reflectsDiagnosticFreeOnSuccess

example := @functionSignature_success_sound
example := @functionSignature_success_sound_and_validFor
example := @functionSignature_module_success_sound
example := @functionSignature_contract_success_sound

example {input next : State} {signature : FunctionSignature}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .module input = .ok signature next) :
    FunctionSignatureParses ModuleFunctionModifiersAllowed
          input.declarativeRemainder signature next.declarativeRemainder ∧
      FunctionSignature.ValidFor input.file signature :=
  functionSignature_success_sound_and_validFor .module inputValid
    diagnosticFree result

example {input next : State} {signature : FunctionSignature}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : functionSignature .contract input = .ok signature next) :
    FunctionSignatureParses ContractFunctionModifiersAllowed
          input.declarativeRemainder signature next.declarativeRemainder ∧
      FunctionSignature.ValidFor input.file signature :=
  functionSignature_success_sound_and_validFor .contract inputValid
    diagnosticFree result

end Solcore.Test.SyntaxParserFunctionSignatureSoundnessProperties
