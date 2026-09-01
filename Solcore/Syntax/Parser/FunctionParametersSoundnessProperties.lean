import Solcore.Syntax.Parser.DelimitedAllowEmptyDiagnosticFreeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.FunctionParameterSoundnessProperties
import Solcore.Syntax.Parser.Signature

/-! Diagnostic-free success soundness for named function-parameter lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free parameter-list success follows the strict grammar. -/
theorem functionParameters_success_sound {input next : State}
    {values : DelimitedList FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionParameters input = .ok values next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
      values next.declarativeRemainder := by
  unfold functionParameters at result
  unfold DeclarativeGrammar.FunctionParametersParses
  exact delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
    .leftParen .rightParen namedParameter
    DeclarativeGrammar.FunctionParameterParses .parameter .topLevel
    namedParameter_success_sound namedParameter_reflectsDiagnosticFreeOnSuccess
    namedParameter_preservesTokenWindow diagnosticFree result

/-- Strict parameter-list grammar soundness composes with source validity. -/
theorem functionParameters_success_sound_and_validFor {input next : State}
    {values : DelimitedList FunctionParameter} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionParameters input = .ok values next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
        values next.declarativeRemainder ∧
      DelimitedList.ValidFor FunctionParameter.ValidFor input.file values := by
  refine ⟨functionParameters_success_sound diagnosticFree result, ?_⟩
  have valid := functionParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
