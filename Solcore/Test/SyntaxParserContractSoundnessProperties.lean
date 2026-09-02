import Solcore.Syntax.Parser.ConstructorDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractDeclSoundnessProperties

/-! External consumers for strict and broad contract-declaration components. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserContractSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @ContractEntryModifiersParses
example := @ContractEntryModifiersOrdinaryParses
example := @ConstructorDeclParses
example := @ConstructorDeclOrdinaryParses
example := @ConstructorDeclRejects
example := @constructorDeclDeterministicOutcomeSpec
example := @FallbackDeclParses
example := @OptionalContractFieldInitializerParses
example := @ContractFieldParses
example := @ContractMemberCoreParses
example := @ContractMemberParses
example := @ContractMemberTailParses
example := @ContractBodyParses
example := @ContractDeclParses

example := @ContractInternals.contractMemberCore_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractMemberCore_success_sound
example := @ContractInternals.contractMemberWithAttribute_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractMemberWithAttribute_success_sound

example := @ContractEntryInternals.entryParameters_success_ordinaryOutcome_sound
example := @ContractEntryInternals.entryParameters_reject_ordinaryOutcome_sound
example := @ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
example := @ContractEntryInternals.implicitPublicModifiers_ne_reject
example := @constructorDecl_success_ordinaryOutcome_sound
example := @constructorDecl_reject_ordinaryOutcome_sound
example := @constructorDecl_ordinaryOutcome_sound
example := @constructorDecl_ordinaryOutcomeSpec

example := @ContractInternals.contractBody_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractBody_success_sound
example := @ContractInternals.contractBody_success_sound_and_validFor

example := @ContractInternals.contractDecl_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractDecl_success_sound
example := @ContractInternals.contractDecl_success_sound_and_validFor

example
    (expressionParses : Remainder → Expr → Remainder → Prop)
    (allowBodyParses requiredBodyParses :
      Remainder → Block → Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {expressionInput expressionNext : State}
      {value : Expr}, expressionNext.diagnosticsRev = [] →
      expression expressionInput = .ok value expressionNext →
      expressionParses expressionInput.declarativeRemainder value
        expressionNext.declarativeRemainder)
    (allowBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (allowBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      allowBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    (requiredBodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .require)))
    (requiredBodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .require) bodyInput = .ok body bodyNext →
      requiredBodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ContractDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : contractDecl input = .ok declaration next) :
    ContractDeclParses expressionParses allowBodyParses requiredBodyParses
          input.declarativeRemainder declaration next.declarativeRemainder ∧
      ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor input.file
        declaration :=
  ContractInternals.contractDecl_success_sound_and_validFor expressionParses
    allowBodyParses requiredBodyParses expressionReflects expressionSound
    allowBodyReflects allowBodySound requiredBodyReflects requiredBodySound
    inputValid diagnosticFree result

example {input next : State} {declaration : ConstructorDecl}
    (result : constructorDecl input = .ok declaration next) :
    ConstructorDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  constructorDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : constructorDecl input = .reject failure rejected) :
    ConstructorDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  constructorDecl_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserContractSoundnessProperties
