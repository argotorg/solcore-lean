import Solcore.Syntax.Parser.FunctionParametersSoundnessProperties

/-! External consumers for typed function-parameter grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserFunctionParameterSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @FunctionParameterParses
example := @FunctionParametersParses

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

example {input next : State} {parameter : FunctionParameter}
    (inputValid : input.ValidFor) (diagnosticFree : next.diagnosticsRev = [])
    (result : namedParameter input = .ok parameter next) :
    FunctionParameterParses input.declarativeRemainder parameter
        next.declarativeRemainder ∧
      parameter.ValidFor input.file :=
  namedParameter_success_sound_and_validFor inputValid diagnosticFree result

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
