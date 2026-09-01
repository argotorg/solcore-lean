import Solcore.Syntax.Parser.FunctionSignatureDiagnosticReflectionProperties
import Solcore.Syntax.Parser.FunctionSignatureSoundnessProperties
import Solcore.Syntax.Parser.TraitProperties

/-! Diagnostic-free success soundness for signature-only trait methods. -/

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

namespace TraitInternals

/-- Trait-method parsing cannot erase an incoming diagnostic. -/
theorem traitMethod_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess traitMethod := by
  unfold traitMethod
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (functionSignature_reflectsDiagnosticFreeOnSuccess .module)
  intro signature
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .topItem)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free trait method follows its signature and semicolon. -/
theorem traitMethod_success_sound {input next : State} {method : TraitMethod}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitMethod input = .ok method next) :
    DeclarativeGrammar.TraitMethodParses input.declarativeRemainder method
      next.declarativeRemainder := by
  unfold traitMethod at result
  rcases bind_ok_components result with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases bind_ok_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have afterSignatureFree := symbol_reflectsDiagnosticFreeOnSuccess
    .semicolon .topItem afterSignature semicolon next semicolonResult
    diagnosticFree
  exact .parsed semicolon.span
    (functionSignature_module_success_sound afterSignatureFree
      signatureResult)
    (symbol_success_exactTokenParses .semicolon .topItem semicolonResult)

/-- Trait-method grammar soundness composes with source validity. -/
theorem traitMethod_success_sound_and_validFor {input next : State}
    {method : TraitMethod} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : traitMethod input = .ok method next) :
    DeclarativeGrammar.TraitMethodParses input.declarativeRemainder method
        next.declarativeRemainder ∧
      TraitMethod.ValidFor input.file method := by
  refine ⟨traitMethod_success_sound diagnosticFree result, ?_⟩
  have valid := traitMethod_validFor input inputValid
  rw [result] at valid
  exact valid.1

end TraitInternals

end Solcore.Syntax.Parser
