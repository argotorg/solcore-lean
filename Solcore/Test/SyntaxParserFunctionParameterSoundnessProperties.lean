import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParametersExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParameterOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParametersOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParametersSoundnessProperties

/-! External consumers for strict and recovery-aware function parameters. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionParameterSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FunctionParameterParses
example := @FunctionParametersParses
example := @FunctionParameterTailOrdinaryParses
example := @FunctionParameterCoreOrdinaryParses
example := @FunctionParameterCoreRejects
example := @FunctionParameterBoundaryStops
example := @FunctionParameterOrdinaryParses
example := @FunctionParameterRejects
example := @functionParameterCoreDeterministicOutcomeSpec
example := @functionParameterDeterministicOutcomeSpec
example := @functionParameterRecoveryExactOutcomeSpec
example := @functionParameterExactOutcomeSpec
example := @FunctionParametersOrdinaryParses
example := @FunctionParametersRejects
example := @functionParametersDeterministicOutcomeSpec
example := @functionParametersExactOutcomeSpec

example := @Parser.ReflectsDiagnosticFreeOnSuccess
example := @Parser.pure_reflectsDiagnosticFreeOnSuccess
example := @Parser.bind_reflectsDiagnosticFreeOnSuccess
example := @Parser.orElse_reflectsDiagnosticFreeOnSuccess
example := @delimited_reflectsDiagnosticFreeOnSuccess
example := @delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
example := @typeExprWithFuel_reflectsDiagnosticFreeOnSuccess
example := @typeExpr_reflectsDiagnosticFreeOnSuccess
example := @namedParameter_reflectsDiagnosticFreeOnSuccess

example := @namedParameter_success_sound
example := @namedParameter_success_sound_and_validFor
example := @functionParameters_success_sound
example := @functionParameters_success_sound_and_validFor
example := @FunctionParameterInternals.namedParameterCore_ordinaryOutcome_sound
example := @FunctionParameterInternals.namedParameterCore_ordinaryOutcomeSpec
example := @namedParameter_success_ordinaryOutcome_sound
example := @namedParameter_reject_ordinaryOutcome_sound
example := @namedParameter_ordinaryOutcome_sound
example := @namedParameter_ordinaryOutcomeSpec
example := @namedParameter_exactOutcomeSpec
example := @namedParameter_success_result_unique
example := @namedParameter_reject_output_unique
example := @functionParameters_success_ordinaryOutcome_sound
example := @functionParameters_reject_ordinaryOutcome_sound
example := @functionParameters_ordinaryOutcome_sound
example := @functionParameters_ordinaryOutcomeSpec
example := @functionParameters_exactOutcomeSpec
example := @functionParameters_success_result_unique
example := @functionParameters_reject_output_unique

example :
    DeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      (FunctionParameterRejects TypeExprRejects) :=
  functionParameterDeterministicOutcomeSpec typeExprDeterministicOutcomeSpec

example :
    ExactDeterministicOutcomeSpec
      (FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects)
      (FunctionParameterRejects TypeExprRejects) :=
  functionParameterExactOutcomeSpec typeExprExactOutcomeSpec

example {input next : State} {parameter : FunctionParameter}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : namedParameter input = .ok parameter next) :
    FunctionParameterParses input.declarativeRemainder parameter
        next.declarativeRemainder ∧
      parameter.ValidFor input.file :=
  namedParameter_success_sound_and_validFor inputValid diagnosticFree result

example {input next : State} {parameter : FunctionParameter}
    (result : namedParameter input = .ok parameter next) :
    FunctionParameterOrdinaryParses TypeExprOrdinaryParses TypeExprRejects
      input.declarativeRemainder parameter next.declarativeRemainder :=
  namedParameter_success_ordinaryOutcome_sound TypeExprOrdinaryParses
    TypeExprRejects typeExpr_success_sound typeExpr_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : namedParameter input = .reject failure rejected) :
    FunctionParameterRejects TypeExprRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  namedParameter_reject_ordinaryOutcome_sound TypeExprRejects
    typeExpr_reject_sound result

example {input next : State}
    {parameters : DelimitedList FunctionParameter}
    (result : functionParameters input = .ok parameters next) :
    FunctionParametersOrdinaryParses input.declarativeRemainder parameters
      next.declarativeRemainder :=
  functionParameters_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : functionParameters input = .reject failure rejected) :
    FunctionParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  functionParameters_reject_ordinaryOutcome_sound result

example {input next : State}
    {parameters : DelimitedList FunctionParameter}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : functionParameters input = .ok parameters next) :
    FunctionParametersParses input.declarativeRemainder parameters
        next.declarativeRemainder ∧
      DelimitedList.ValidFor FunctionParameter.ValidFor input.file
        parameters :=
  functionParameters_success_sound_and_validFor inputValid diagnosticFree
    result

end Solcore.Test.SyntaxParserFunctionParameterSoundnessProperties
