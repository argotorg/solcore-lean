import Solcore.Syntax.Parser.ImplDeclSoundnessProperties
import Solcore.Syntax.Parser.ImplDeclarationOrdinaryOutcomeSoundnessProperties

/-! External consumers for strict and broad implementation soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserImplSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalImplDefaultMarkerParses
example := @OptionalImplDefaultMarkerOrdinaryParses
example := @OptionalImplDefaultMarkerRejects
example := @optionalImplDefaultMarkerDeterministicOutcomeSpec
example := @OptionalImplDefaultMarkerOrdinaryParses.value_unique
example := @OptionalImplDefaultMarkerOrdinaryParses.result_unique
example := @OptionalImplDefaultMarkerRejects.output_unique
example := @optionalImplDefaultMarkerExactOutcomeSpec
example := @ImplHeadArgumentsParses
example := @ImplHeadArgumentsOrdinaryParses
example := @ImplHeadArgumentsRejects
example := @implHeadArgumentsDeterministicOutcomeSpec
example := @ImplHeadArgumentsOrdinaryParses.value_unique
example := @ImplHeadArgumentsOrdinaryParses.result_unique
example := @ImplHeadArgumentsRejects.output_unique
example := @implHeadArgumentsExactOutcomeSpec
example := @ImplMethodParses
example := @ImplMethodOrdinaryParses
example := @ImplMethodRejects
example := @implMethodDeterministicOutcomeSpec
example := @ImplMethodTailParses
example := @ImplMethodStartAt
example := @ImplMethodTailOrdinaryParses
example := @ImplMethodTailOrdinaryOutcomeParses
example := @ImplMethodTailRejects
example := @implMethodTailDeterministicOutcomeSpec
example := @ImplMethodTailOrdinaryParses.result_unique
example := @ImplMethodTailOrdinaryOutcomeParses.value_unique
example := @ImplMethodTailRejects.output_unique
example := @implMethodTailExactOutcomeSpecOfMethod
example := @ImplBodyParses
example := @ImplBodyOrdinaryParses
example := @ImplBodyOrdinaryOutcomeParses
example := @ImplBodyRejects
example := @implBodyDeterministicOutcomeSpec
example := @ImplBodyOrdinaryParses.result_unique
example := @ImplBodyOrdinaryOutcomeParses.value_unique
example := @ImplBodyRejects.output_unique
example := @implBodyExactOutcomeSpecOfMethod
example := @implBodyExactOutcomeSpecOfBody
example := @implBodyExactOutcomeSpecOfStatementFuel
example := @ImplDeclParses
example := @ImplDeclOrdinaryParses
example := @ImplDeclRejects
example := @implDeclDeterministicOutcomeSpec
example := @ImplDeclOrdinaryParses.value_unique_of_impl_body
example := @ImplDeclOrdinaryParses.result_unique_of_impl_body
example := @ImplDeclRejects.output_unique_of_impl_body
example := @implDeclExactOutcomeSpecOfImplBody
example := @implDeclExactOutcomeSpecOfBody
example := @implDeclExactOutcomeSpecOfStatementFuel

example := @ImplInternals.implDefaultMarker_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implDefaultMarker_success_sound
example := @ImplInternals.implDefaultMarker_validFor
example := @ImplInternals.requireImplArguments_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.requireImplArguments_success_shape
example := @ImplInternals.requireImplArguments_reply_validFor
example := @ImplInternals.implHeadArguments_success_sound
example := @ImplInternals.implDefaultMarker_success_ordinaryOutcome_sound
example := @ImplInternals.implDefaultMarker_reject_ordinaryOutcome_sound
example := @ImplInternals.implDefaultMarker_ordinaryOutcome_sound
example := @ImplInternals.implDefaultMarker_ordinaryOutcomeSpec
example := @ImplInternals.implDefaultMarker_exactOutcomeSpec
example := @ImplInternals.implDefaultMarker_success_result_unique
example := @ImplInternals.implDefaultMarker_reject_output_unique
example := @ImplInternals.implHeadArguments_success_ordinaryOutcome_sound
example := @ImplInternals.implHeadArguments_reject_ordinaryOutcome_sound
example := @ImplInternals.implHeadArguments_ordinaryOutcome_sound
example := @ImplInternals.implHeadArguments_ordinaryOutcomeSpec
example := @ImplInternals.implHeadArguments_exactOutcomeSpec
example := @ImplInternals.implHeadArguments_success_result_unique
example := @ImplInternals.implHeadArguments_reject_output_unique

example := @ImplInternals.implMethod_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implMethod_success_sound
example := @ImplInternals.implMethod_success_sound_and_validFor
example := @ImplInternals.implMethod_validFor
example := @ImplInternals.implMethod_success_ordinaryOutcome_sound
example := @ImplInternals.implMethod_reject_ordinaryOutcome_sound
example := @ImplInternals.implMethod_ordinaryOutcome_sound
example := @ImplInternals.implMethod_ordinaryOutcomeSpec
example := @implMethodExactOutcomeSpecOfBody
example := @implMethodExactOutcomeSpecOfStatementFuel
example := @ImplInternals.implMethod_exactOutcomeSpec_of_body
example := @ImplInternals.implMethod_exactOutcomeSpec_of_statementFuel
example := @ImplInternals.implMethod_success_result_unique_of_body
example := @ImplInternals.implMethod_reject_output_unique_of_body

example := @ImplInternals.implBody_reflectsDiagnosticFreeOnSuccess
example := @ImplInternals.implBody_success_sound
example := @ImplInternals.implBody_success_sound_and_validFor
example := @ImplInternals.implBody_validFor
example := @ImplInternals.implBody_success_ordinaryOutcome_sound
example := @ImplInternals.implBody_reject_ordinaryOutcome_sound
example := @ImplInternals.implBody_ordinaryOutcome_sound
example := @ImplInternals.implBody_ordinaryOutcomeSpec
example := @ImplInternals.implBody_exactOutcomeSpec_of_method
example := @ImplInternals.implBody_exactOutcomeSpec_of_body
example := @ImplInternals.implBody_exactOutcomeSpec_of_statementFuel
example := @ImplInternals.implBody_success_result_unique_of_method
example := @ImplInternals.implBody_reject_output_unique_of_method
example := @ImplInternals.implBody_success_result_unique_of_body
example := @ImplInternals.implBody_reject_output_unique_of_body
example := @ImplInternals.implBody_success_result_unique_of_statementFuel
example := @ImplInternals.implBody_reject_output_unique_of_statementFuel

example := @implDecl_reflectsDiagnosticFreeOnSuccess
example := @implDecl_success_sound
example := @implDecl_success_sound_and_validFor
example := @implDecl_validFor
example := @implDecl_success_ordinaryOutcome_sound
example := @implDecl_reject_ordinaryOutcome_sound
example := @implDecl_ordinaryOutcome_sound
example := @implDecl_ordinaryOutcomeSpec
example := @implDecl_exactOutcomeSpec_of_implBody
example := @implDecl_exactOutcomeSpec_of_body
example := @implDecl_exactOutcomeSpec_of_statementFuel
example := @implDecl_success_result_unique_of_implBody
example := @implDecl_reject_output_unique_of_implBody
example := @implDecl_success_result_unique_of_body
example := @implDecl_reject_output_unique_of_body
example := @implDecl_success_result_unique_of_statementFuel
example := @implDecl_reject_output_unique_of_statementFuel

example
    (statementValid : SourceFile → Statement → Prop)
    (bodyParses : Remainder → Block → Remainder → Prop)
    (bodyValid : (block .allow).ValidFor (Block.ValidFor statementValid))
    (bodyWindow : Parser.PreservesTokenWindow (block .allow))
    (bodyReflects : Parser.ReflectsDiagnosticFreeOnSuccess
      (isolateBlock (block .allow)))
    (bodySound : ∀ {bodyInput bodyNext : State} {body : Block},
      bodyNext.diagnosticsRev = [] →
      isolateBlock (block .allow) bodyInput = .ok body bodyNext →
      bodyParses bodyInput.declarativeRemainder body
        bodyNext.declarativeRemainder)
    {input next : State} {declaration : ImplDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : implDecl input = .ok declaration next) :
    ImplDeclParses bodyParses input.declarativeRemainder declaration
          next.declarativeRemainder ∧
      ImplDecl.ValidFor statementValid input.file declaration :=
  implDecl_success_sound_and_validFor statementValid bodyParses bodyValid
    bodyWindow bodyReflects bodySound inputValid diagnosticFree result

example {input next : State} {method : ImplMethod}
    (result : ImplInternals.implMethod input = .ok method next) :
    ImplMethodOrdinaryParses input.declarativeRemainder method
      next.declarativeRemainder :=
  ImplInternals.implMethod_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : ImplInternals.implMethod input = .reject failure rejected) :
    ImplMethodRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  ImplInternals.implMethod_reject_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : implDecl input = .reject failure rejected) :
    ImplDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  implDecl_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserImplSoundnessProperties
