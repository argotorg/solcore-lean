import Solcore.Syntax.Parser.ConstructorDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractDeclSoundnessProperties
import Solcore.Syntax.Parser.ContractFieldOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.ContractBodyOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTermPublicOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FallbackDeclarationOrdinaryOutcomeSoundnessProperties

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
example := @FallbackParameterValidationOrdinaryParses
example := @FallbackDeclOrdinaryParses
example := @FallbackDeclRejects
example := @fallbackDeclDeterministicOutcomeSpec
example := @OptionalContractFieldInitializerParses
example := @OptionalContractFieldInitializerOrdinaryParses
example := @OptionalContractFieldInitializerRejects
example := @optionalContractFieldInitializerDeterministicOutcomeSpec
example := @ContractFieldParses
example := @ContractFieldOrdinaryParses
example := @ContractFieldRejects
example := @contractFieldDeterministicOutcomeSpec
example := @ContractMemberCoreTokenPresentAt
example := @ContractMemberCoreOrdinaryParses
example := @ContractMemberCoreRejects
example := @contractMemberCoreDeterministicOutcomeSpec
example := @ContractDeriveAttaches
example := @ContractMemberOrdinaryParses
example := @ContractMemberRejects
example := @contractMemberDeterministicOutcomeSpec
example := @ContractMemberRecoveryBoundaryStartsAt
example := @ContractMemberRecoveryStops
example := @ContractMemberRecoveryScanParses
example := @ContractMemberRecoveryParses
example := @ContractMemberRecoveryRejects
example := @contractMemberRecoveryDeterministicOutcomeSpec
example := @ContractMemberRejectsWithPreservedWindow
example := @ContractMemberTailOrdinaryParses
example := @ContractMemberTailOrdinaryOutcomeParses
example := @ContractMemberTailRejects
example := @contractMemberTailDeterministicOutcomeSpec
example := @ContractBodyOrdinaryParses
example := @ContractBodyOrdinaryOutcomeParses
example := @ContractBodyRejects
example := @contractBodyDeterministicOutcomeSpec
example := @ContractMemberCoreParses
example := @ContractMemberParses
example := @ContractMemberTailParses
example := @ContractBodyParses
example := @ContractDeclParses

example := @ContractInternals.contractMemberCore_reflectsDiagnosticFreeOnSuccess
example := @ContractInternals.contractMemberCore_success_sound
example := @ContractInternals.contractMemberCore_success_ordinaryOutcome_sound
example := @ContractInternals.contractMemberCore_reject_ordinaryOutcome_sound
example := @ContractInternals.contractMemberCore_ordinaryOutcome_sound
example := @ContractInternals.contractMemberCore_ordinaryOutcomeSpec
example := @ContractInternals.attachContractDerive_success_ordinaryOutcome_sound
example := @ContractInternals.attachContractDerive_total_success
example := @ContractInternals.contractMemberWithAttribute_success_ordinaryOutcome_sound
example := @ContractInternals.contractMemberWithAttribute_reject_ordinaryOutcome_sound
example := @ContractInternals.contractMemberWithAttribute_ordinaryOutcome_sound
example := @ContractInternals.contractMemberWithAttribute_ordinaryOutcomeSpec
example := @ContractInternals.recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true
example := @ContractInternals.atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt
example := @ContractInternals.contractMemberRecoveryStops_of_guard_eq_true
example := @ContractInternals.contractMemberRecoveryStops_of_advance?_eq_none
example := @ContractInternals.no_contractMemberRecoveryStops_of_nonBoundary_token
example := @ContractInternals.recoverContractMemberAux_success_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_success_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_reject_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_ordinaryOutcome_sound
example := @ContractInternals.recoverContractMember_ordinaryOutcomeSpec
example := @ContractInternals.contractMemberRejectsWithPreservedWindow_of_result
example := @ContractInternals.rewoundContractMember_declarativeRemainder_eq
example := @ContractInternals.cursor_lt_endIndex_of_atEnd_eq_false
example := @ContractInternals.contractMemberRecoveryBoundaryStartsAt_of_guard_eq_true
example := @ContractInternals.no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
example := @ContractInternals.closeContractBody_success_exact
example := @ContractInternals.closeContractBody_success_of_rightBrace_guard
example := @ContractInternals.contractMembers_success_ordinaryOutcome_sound_strong
example := @ContractInternals.contractMembers_reject_ordinaryOutcome_sound
example := @ContractInternals.contractBody_success_ordinaryOutcome_sound
example := @ContractInternals.contractBody_reject_ordinaryOutcome_sound
example := @ContractInternals.contractBody_ordinaryOutcome_sound
example := @ContractInternals.contractBody_ordinaryOutcomeSpec
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
example := @fallbackDecl_success_ordinaryOutcome_sound
example := @fallbackDecl_reject_ordinaryOutcome_sound
example := @fallbackDecl_ordinaryOutcome_sound
example := @fallbackDecl_ordinaryOutcomeSpec
example := @ContractInternals.optionalFieldInitializer_success_ordinaryOutcome_sound
example := @ContractInternals.optionalFieldInitializer_reject_ordinaryOutcome_sound
example := @ContractInternals.optionalFieldInitializer_ordinaryOutcome_sound
example := @ContractInternals.optionalFieldInitializer_ordinaryOutcomeSpec
example := @ContractInternals.contractField_success_ordinaryOutcome_sound
example := @ContractInternals.contractField_reject_ordinaryOutcome_sound
example := @ContractInternals.contractField_ordinaryOutcome_sound
example := @ContractInternals.contractField_ordinaryOutcomeSpec

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

example {input next : State} {member : ContractMember}
    (result : ContractInternals.contractMemberCore input = .ok member next) :
    ContractMemberCoreOrdinaryParses input.declarativeRemainder member
      next.declarativeRemainder :=
  ContractInternals.contractMemberCore_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractMemberCore input =
      .reject failure rejected) :
    ContractMemberCoreRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  ContractInternals.contractMemberCore_reject_ordinaryOutcome_sound result

example {derive : DeriveAttribute} {coreMember attached : ContractMember}
    {input output : State}
    (result : ContractInternals.attachContractDerive derive coreMember input =
      .ok attached output) :
    ContractDeriveAttaches derive coreMember attached ∧
      output.declarativeRemainder = input.declarativeRemainder :=
  ContractInternals.attachContractDerive_success_ordinaryOutcome_sound result

example {input output : State} {member : ContractMember}
    (result : ContractInternals.contractMemberWithAttribute input =
      .ok member output) :
    ContractMemberOrdinaryParses input.declarativeRemainder member
      output.declarativeRemainder :=
  ContractInternals.contractMemberWithAttribute_success_ordinaryOutcome_sound
    result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractMemberWithAttribute input =
      .reject failure rejected) :
    ContractMemberRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  ContractInternals.contractMemberWithAttribute_reject_ordinaryOutcome_sound
    result

example {input output : State} {member : ContractMember}
    (result : ContractInternals.recoverContractMember input =
      .ok member output) :
    ContractMemberRecoveryParses input.declarativeRemainder member
      output.declarativeRemainder :=
  ContractInternals.recoverContractMember_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.recoverContractMember input =
      .reject failure rejected) :
    ContractMemberRecoveryRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  ContractInternals.recoverContractMember_reject_ordinaryOutcome_sound result

example {input output : State} {body : ContractInternals.ContractBody}
    (result : ContractInternals.contractBody input = .ok body output) :
    ContractBodyOrdinaryParses input.declarativeRemainder body.span body.members
      output.declarativeRemainder :=
  ContractInternals.contractBody_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractBody input = .reject failure rejected) :
    ContractBodyRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  ContractInternals.contractBody_reject_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : constructorDecl input = .reject failure rejected) :
    ConstructorDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  constructorDecl_reject_ordinaryOutcome_sound result

example {input next : State} {declaration : FallbackDecl}
    (result : fallbackDecl input = .ok declaration next) :
    FallbackDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  fallbackDecl_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : fallbackDecl input = .reject failure rejected) :
    FallbackDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  fallbackDecl_reject_ordinaryOutcome_sound result

example {input next : State} {initializer : Option Expr}
    (result : ContractInternals.optionalFieldInitializer expression input =
      .ok initializer next) :
    OptionalContractFieldInitializerOrdinaryParses
      CoreExpressionOrdinaryParses input.declarativeRemainder initializer
        next.declarativeRemainder :=
  ContractInternals.optionalFieldInitializer_success_ordinaryOutcome_sound
    expression CoreExpressionOrdinaryParses expression_success_ordinary_sound
      result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.optionalFieldInitializer expression input =
      .reject failure rejected) :
    OptionalContractFieldInitializerRejects CoreExpressionPublicRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  ContractInternals.optionalFieldInitializer_reject_ordinaryOutcome_sound
    expression CoreExpressionPublicRejects expression_reject_ordinary_sound
      result

example {input next : State} {field : ContractField}
    (result : ContractInternals.contractField expression input =
      .ok field next) :
    ContractFieldOrdinaryParses CoreExpressionOrdinaryParses
      input.declarativeRemainder field next.declarativeRemainder :=
  ContractInternals.contractField_success_ordinaryOutcome_sound expression
    CoreExpressionOrdinaryParses expression_success_ordinary_sound result

example {input rejected : State} {failure : Failure}
    (result : ContractInternals.contractField expression input =
      .reject failure rejected) :
    ContractFieldRejects CoreExpressionOrdinaryParses
      CoreExpressionPublicRejects input.declarativeRemainder
        rejected.declarativeRemainder :=
  ContractInternals.contractField_reject_ordinaryOutcome_sound expression
    CoreExpressionOrdinaryParses CoreExpressionPublicRejects
      expression_success_ordinary_sound expression_reject_ordinary_sound result

end Solcore.Test.SyntaxParserContractSoundnessProperties
